(define-module (pamphlet)
  #:use-module (ice-9 nice-9)
  #:use-module (srfi srfi-1)
  #:use-module (system base compile)
  #:export (assert
	    e.g.
	    publish
	    argmin
	    argmax
	    min+max
	    argmin+argmax
	    skip
	    alter
	    generate-list
	    list<-values
	    measured
	    now
	    with-default
	    without-default
	    specify
	    rest
	    equivalence-classes
	    subsets
	    hash-map->alist
	    number->symbol
	    ->string
	    sum
	    product
	    fold-left
	    fold-right
	    scan
	    prefix-sum
	    extend-left
	    extend-right
	    in?
	    indexed
	    multicombinations
	    )
  #:re-export (every
	       any
	       filter-map
	       append-map
	       concatenate
	       reduce
	       take
	       drop
	       partition
	       split-at
	       iota
	       count
	       first
	       )
  #:replace ((compose/values . compose)))

(define* (expand-form e #:key (opts '()))
  (let ((exp env (decompile
                  (compile e #:from 'scheme
                    #:to 'tree-il
                    #:env (current-module))
                  #:from 'tree-idl
                  #:to 'scheme
                  #:opts opts)))
    exp))

(define-syntax (expand expression)
  (expand-form 'expression))

(define-syntax (assert proposition)
  (begin))

(define-syntax e.g. (===> ~~~>)
  ((_ example)
   (or example
       (error 'example)))
  ((_ example ===> value)
   (let ((result example))
     (if (equal? result 'value)
	 result
	 (error '(example ===> value)))))

  ((_ example ===> values ...)
   (call-with-values (lambda () example)
     (lambda results (equal? results '(values ...)))))

  ((_ example ~~~> value) ;; the ~~~> reads as "may nondeterministically
   example)) ;; evaluate to"

;; The `publish' macro is used to provide means to separate public
;; definitions from private ones (such that are visible only from within
;; the public procedures and from within themselves).
;; For example, the form
;; 
;; (publish
;;   (define (f x) (+ a x))
;;   (define (g y) (* a y))
;;  where
;;   (define a 5))
;;
;; is equivalent to
;;
;; (begin
;;   (define f (and (defined? 'f) f))
;;   (define g (and (defined? 'g) g))
;;   (let ()
;;     (define a 5)
;;     (set! f (let () (define (f x) (+ a x)) f))
;;     (set! g (let () (define (g x) (* a y)) g))))

(define-syntax (publish definitions ...)
  (publisher (definitions ...) ()))

(define-syntax publisher (where)
  ((_ (where private ...) (public ...))
   (private+public (private ...) (public ...)))
  ((_ (new defs ...) (approved ...))
   (publisher (defs ...) 
	      (approved ... new))))

(define-syntax private+public
  (lambda (stx)
    (define (sorted-private/interfaces+names+bodies private specs)
      ;; both sorting and name extraction takes place in the
      ;; same function called from with-syntax, because that
      ;; way we can tell the macro processor that the bindings in
      ;; the code belong to the same scope
      (define (interface-name interface)
	(match interface
	  ((head . tail)
	   (interface-name head))
	  ((? symbol? name)
	   name)))
      `(,(datum->syntax ;; this reordering is done, so that the (e.g. ...)
	  stx ;; forms can be freely mixed with definitions
	  (let ((definitions non-definitions
		  (partition (lambda (prototype)
			       (match prototype
				 (((? symbol? x) . _)
				  (string-contains (symbol->string x)
						   "def"))
				 (_ #f)))
			     (syntax->datum private))))
	    `(,@definitions ,@non-definitions)))
	,(map (lambda (spec)
		(syntax-case spec ()
		  ((interface . body)
		   (datum->syntax stx `(,(syntax->datum #'interface)
					,(interface-name 
					  (syntax->datum #'interface))
					,(syntax->datum #'body))))))
	      specs)))
    (syntax-case stx ()
      ((_ (private ...) ((define-variant . spec) ...))
       (with-syntax ((((private ...) ((interface name body) ...))
		      (sorted-private/interfaces+names+bodies 
		       #'(private ...) #'(spec ...))))
	 #'(begin
	     (define name (and (defined? 'name) name))
	     ...
	     (let ()
	       private ...
	       (set! name
		     (let ()
		       (define-variant interface . body)
		       name))
	       ...)))))))

(define (hash-map->alist hash)
  (hash-map->list cons hash))

(define (number->symbol n)
  (let* ((n (if (exact? n) (exact->inexact n) n))
	 (s (number->string n)))
    (string->symbol
     (string-take s (min (string-length s) 4)))))

(define rest cdr)

(publish
 (define (argmin property element . elements)
   (apply argopt < property element elements))
 (define (argmax property element . elements)
   (apply argopt > property element elements))
 where
 (define (argopt < property element . elements)
   (let next-trial ((champion element)
		    (mastery (property element))
		    (opponents elements))
     (if (null? opponents)
	 (values champion mastery)
	 (let* ((rival (first opponents))
		(challenge (property rival)))
	   (if (< challenge mastery)
	       (next-trial rival challenge (rest opponents))
	       (next-trial champion mastery (rest opponents))))))))

(e.g.
 (argmin length '(1 2) '(3) '(4 5 6))
 ===> (3))

(define (min+max first . args)
  (assert (and (number? first)
	       (every number? args)))
  (let loop ((min first)
	     (max first)
	     (remaining args))
    (match remaining
      (()
       (values min max))
      ((current . remaining)
       (cond ((< current min)
	      (loop current max remaining))
	     ((> current max)
	      (loop min current remaining))
	     (else
	      (loop min max remaining)))))))

(e.g.
 (min+max 5 4 6 3 7 2 8 1)
 ===> 1 8)

(define (argmin+argmax property element . elements)
  (let ((quality (property element)))
    (let next-trial ((winner element)
		     (looser element)
		     (mastery quality)
		     (failure quality)
		     (opponents elements))
      (if (null? opponents)
	  (values looser winner)
	  (let* ((rival (first opponents))
		 (quality (property rival)))
	    (cond ((< quality failure)
		   (next-trial winner rival mastery quality (rest opponents)))
		  ((> quality mastery)
		   (next-trial rival looser quality failure (rest opponents)))
		  (else
		   (next-trial winner looser mastery failure 
			       (rest opponents)))))))))

(e.g.
 (argmin+argmax length '(1 2) '(3) '(4 5 6))
 ===> (3) (4 5 6))

(define (skip #;element-number n #;in list)
  (let (((head . tail) list))
    (if (= n 0)
	tail
	`(,head . ,(skip #;element-number (- n 1) #;in tail)))))

(e.g. (skip #;element-number 1 #;in '(a b c)) ===> (a c))

(define (alter #;element-number n #;in list #;with replacement)
  (assert (and (integer? n) (>= n 0)))
  (let (((head . tail) list))
    (if (= n 0)
	`(,replacement . ,tail)
	`(,head . ,(alter #;element-number (- n 1) 
					   #;in tail #;with replacement)))))

(e.g.
 (alter #;element-number 1 #;in '(ząb dupa zębowa) #;with 'zupa)
 ===> (ząb zupa zębowa))

(define (generate-list n generator)
  (assert (and (integer? size) (>= size 0)))
  (if (= n 0)
      '()
      `(,(generator) . ,(generate-list (- n 1) generator))))

(define-syntax (list<-values values)
  (call-with-values (lambda () values) list))

(define now get-internal-real-time)

(define-syntax (measured expression)
  (let ((starting-time (now)))
    (let ((result (list<-values expression)))
      (format #t "~s: ~s ns\n" 'expression (- (now) starting-time))
      (apply values result))))

(define SPECIFIC-CONTEXT (make-hash-table))

(let-syntax (((specific-literal-syntax binding-structure name value)
	      (lambda (stx)
		(assert (appears? #'name #;in #'binding-structure))
		(syntax-case stx ()
		  ((_ (binding-structure (... ...)) actions . *)
		   (with-syntax ((specific (datum->syntax stx 'specific)))
		     #'(let-syntax 
			   ((specific
			     (syntax-rules (name (... ...))
			       ((_ name)
				(let ((default (hash-ref
						 SPECIFIC-CONTEXT
						'name '())))
				  (if (null? default)
				      value
				      (first default))))
			       (... ...))))
			 actions . *)))))))
  (define-syntax with-default 
    (specific-literal-syntax (name value) name value))
  (define-syntax without-default 
    (specific-literal-syntax 
     name name (throw 'unspecified #:name 'name
		      #:context (hash-map->alist SPECIFIC-CONTEXT)))))

(define-syntax specify
  (lambda (stx)
    (syntax-case stx ()
      ((_ ((name expression) ...)
	  actions ...)
       (with-syntax (((value ...) (generate-temporaries #'(expression ...))))
	 #'(let ((value expression) ...)
	     (dynamic-wind
	       (lambda ()
		 (hash-set! SPECIFIC-CONTEXT 'name
			    (cons value (hash-ref SPECIFIC-CONTEXT 'name '())))
		 ...)
	       (lambda ()
		 actions ...)
	       (lambda ()
		 (hash-set! SPECIFIC-CONTEXT 'name
			    (rest (hash-ref SPECIFIC-CONTEXT 'name)))
		 ...))))))))

(e.g.                                   ; this is how the trio 'with-default',
 (let ()                                ; 'specific' and 'specify' can be used
   (with-default ((x 10)
		  (y 20))
     (define (f)
       `(,(specific x) ,(specific y))))
   (specify ((x 30))
     (f)))
 ===> (30 20))

(define (equivalence-classes equivalent? set)
  (let next-item ((set set)(result '()))
    (match set
      (()
       (reverse (map reverse result)))
      ((item . set)
       (match result
	 (()
	  (next-item set `((,item) . ,result)))
	 ((this . next)
	  (let next-class ((past '()) (present this) (future next))
	    (match present
	      ((paradigm . _)
	       (if (equivalent? item paradigm)
		   (next-item set `((,item . ,present)
				    . (,@past ,@future)))
		   (match future
		     (()
		      (next-item set `((,item) ,@result)))
		     ((this . next)
		      (next-class `(,present . ,past) this next)))
		   )))
	    )))))))

(e.g.
 (equivalence-classes (lambda(x y)(= (modulo x 3) (modulo y 3))) (iota 9))
 ===> ((0 3 6) (1 4 7) (2 5 8)))

(define (subsets l n)
  (cond
   ((= n 0) '())
   ((= n 1) (map list l))
   ((> n 1)
    (match l
      (() '())
      ((first . rest)
       (append (map (lambda (next) 
		      `(,first . ,next))
		    (subsets rest (1- n)))
	       (subsets rest n)))))))

(define (impose-arity n procedure)
  (let ((new-procedure (lambda args (apply procedure args))))
    (set-procedure-property! new-procedure 'name
			     (or (procedure-name procedure)
				 'fixed-arity))
    (set-procedure-property! new-procedure 'imposed-arity
			     (if (list? n) n `(,n 0 #f)))
    new-procedure))

(define (arity procedure)
  (assert (procedure? procedure))
  (or (procedure-property procedure 'imposed-arity)
      (procedure-property procedure 'arity)))

(define (clip args #;to arity)
  (match arity
    ((min _ #f)
     (take args min))
    ((? number?)
     (take args arity))
    (_
     args)))

(define (compose/values . fns)
  (define (make-chain fn chains)
    (impose-arity
     (arity fn)
     (lambda args
       (call-with-values 
	   (lambda () (apply fn args))
	 (lambda vals (apply chains (clip vals (arity chains))))))))
  (let ((composer (reduce make-chain values fns)))
    composer))

(define (->string object)
  (cond ((symbol? object)
	 (symbol->string object))
	((number? object)
	 (number->string object))
	((list? object)
	 (string-append
	  "(" (string-join (map ->string object) " ") ")"))
	((pair? object)
	 (string-append
	  "(" (->string (car object)) " . " (->string (cdr object))))
	((string? object)
	 object)
	((vector? object)
	 (string-append "#" (->string (vector->list object))))
	(else
	 (with-output-to-string
	   (lambda ()
	     (display object))))))


(define (fold-left op e . ls)
  (match ls
    (((heads . tails) ...)
     (apply fold-left op (apply op e heads) tails))
    (_
     e)))

(define (fold-right op e . ls)
  (match ls
    (((heads . tails) ...)
     (apply op (apply fold-right op e tails) heads))
    (_
     e)))

(define (sum elements)
  (fold-left + 0 elements))

(define (product elements)
  (fold-left * 1 elements))

(define (scan op e l)
  (match l
    (()
     '())
    ((h . t)
     (let ((e* (op e h)))
       `(,e* . ,(scan op e* t))))))

(e.g.
 (scan * 1 '(1 2 3 4 5 6)) ===> (1 2 6 24 120 720))

(define (prefix-sum l)
  (scan + 0 l))

(define* (extend-right l #;to size #;with #:optional (fill #f))
  (let ((extension-size (- size (length l))))
    (if (< extension-size 0)
	(error "list length exceeds the desired length")
	`(,@l ,@(make-list extension-size fill)))))

(e.g. (extend-right '(1 2 3) 5 0) ===> (1 2 3 0 0))

(define* (extend-left l #;to size #;with #:optional (fill #f))
  (let ((extension-size (- size (length l))))
    (if (< extension-size 0)
	(error "list length exceeds the desired length")
	`(,@(make-list extension-size fill) ,@l))))

(e.g. (extend-left '(1 2 3) 5 0) ===> (0 0 1 2 3))

(define ((in? set) element)
  (match set
    ((first . rest)
     (or (equal? element first)
	 ((in? rest) element)))
    (_
     #f)))

(e.g. ((in? '(a b c)) 'a))

(e.g. (not ((in? '(a b c)) 'd)))

(define (indexed list)
  (zip (iota (length list)) list))

(e.g. (indexed '(a b c)) ===> ((0 a) (1 b) (2 c)))

(define (multicombinations #;from-set A #;of-length n)
  (assert (not (contains-duplicates? A)))
  (cond ((= n 0)
	 '())
	((= n 1)
	 (map list A))
	(else
	 (append-map (lambda (combination)
		       (map (lambda (a)
			      `(,a . ,combination)) A))
		     (multicombinations #;from-set A #;of-length (- n 1))))))

(e.g.
 (multicombinations #;from-set '(a b) #;of-length 3)
 ===>
 ((a a a) (b a a) (a b a) (b b a) (a a b) (b a b) (a b b) (b b b)))
