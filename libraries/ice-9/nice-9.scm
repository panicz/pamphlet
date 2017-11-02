(define-module (ice-9 nice-9)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:re-export (match)
  #:export ((and-let*/match . and-let*)
	    primitive-lambda)
  #:replace ((cdefine . define)
	     (mlambda . lambda)
	     (named-match-let-values . let)
	     (match-let*-values . let*)
	     (letrec-syntax/rules . letrec-syntax)
	     (let-syntax/rules . let-syntax)
	     (define-syntax/rules . define-syntax)))

;; This module extends the syntax of a few core forms so that their
;; "abuses" behave meaningfully -- in particular, it allows to
;; destructure bindings in "lambda" and "let" forms and use curried definitions.
;; It also provides pattern-matching version of "and-let*".

(define-syntax define-syntax/rules
  (syntax-rules ()
    ((_ (name . pattern) template)
     (define-syntax name
       (syntax-rules ()
	 ((name . pattern) template))))

    ((_ name transformer)
     (define-syntax name transformer))

    ((_ name keywords (pattern template) ...)
     (define-syntax name
       (syntax-rules keywords
	 (pattern
	  template)
	 ...)))
    ))

(define-syntax let*-syntax/rules
  (syntax-rules ()
    ((_ let*-syntax () processed-bindings body . *)
     (let*-syntax processed-bindings body . *))
    
    ((_ let*-syntax (((name pattern ...) template) bindings ...) 
	(processed ...) body . *)
     (let*-syntax/rules
      let*-syntax
      (bindings ...) 
      (processed ... (name (syntax-rules () 
			     ((_ pattern ...) 
			      template))))
      body . *))

    ((_ let*-syntax ((name value) bindings ...) (processed ...) body . *)
     (let*-syntax/rules
      let*-syntax
      (bindings ...) 
      (processed ... (name value))
      body . *))

    ((_ let*-syntax ((name keywords (pattern template) ...) bindings ...)
	(processed ...)
	body . *)
     (let*-syntax/rules
      let*-syntax
      (bindings ...)
      (processed ... (name (syntax-rules keywords 
			     (pattern 
			      template) 
			     ...)))
      body . *))
    ))

(define-syntax let-syntax/rules
  (syntax-rules ()
    ((_ (bindings ...) body . *)
     (let*-syntax/rules let-syntax (bindings ...) () body . *))))

(define-syntax letrec-syntax/rules
  (syntax-rules ()
    ((_ (bindings ...) body . *)
     (let*-syntax/rules letrec-syntax (bindings ...) () body . *))))

(define-syntax mlambda
  (lambda (stx)
    (syntax-case stx ()

      ((_ (first-arg ... last-arg . rest-args) . body)
       (and (every identifier? #'(first-arg ... last-arg))
	    (or (identifier? #'rest-args) (null? #'rest-args)))
       #'(lambda (first-arg ... last-arg . rest-args) . body))

      ((_ arg body ...)
       (or (identifier? #'arg) (null? #'arg))
       #'(lambda arg body ...))

      ((_ args body ...)
       #'(match-lambda* (args body ...) 
	   (_ (error 'mlambda (current-source-location) '(args body ...)))))
      )))

(define-syntax primitive-lambda
  (syntax-rules ()
    ((_ . whatever)
     (lambda . whatever))))

(define-syntax cdefine
  (syntax-rules ()
    ((_ ((head . tail) . args) body ...)
     (cdefine (head . tail)
       (mlambda args body ...)))
    ((_ (name . args) body ...)
     (define name (mlambda args body ...)))
    ((_ . rest)
     (define . rest))
    ))


(define-syntax list<-values
  (syntax-rules ()
    ((_ call)
     (call-with-values (lambda () call) list))))

(define-syntax match-let/error
  (syntax-rules ()
    ((_ ((structure expression) ...)
	body + ...)
     ((match-lambda* ((structure ...) body + ...)
	(_ (error 'match-let/error (current-source-location) 
		  '((structure expression) ...))))
      expression ...))))

(define-syntax named-match-let-values
  (lambda (stx)
    (syntax-case stx ()
      ((_ ((identifier expression) ...) ;; optimization: plain "let" form
	  body + ...)
       (every identifier? #'(identifier ...))
       #'(let ((identifier expression) ...)
	   body + ...))

      ((_ name ((identifier expression) ...) ;; optimization: regular named-let
	  body + ...)
       (and (identifier? #'name) (every identifier? #'(identifier ...)))
       #'(let name ((identifier expression) ...)
	   body + ...))

      ((_ name ((structure expression) ...)
	  body + ...)
       (identifier? #'name)
       #'(letrec ((name (mlambda (structure ...) body + ...)))
	   (name expression ...)))

      ((_ ((structure expression) ...)
	  body + ...)
       #'(match-let/error ((structure expression) ...) 
			  body + ...))

      ((_ ((identifier identifiers ... expression)) body + ...)
       (every identifier? #'(identifier identifiers ...))
       #'(call-with-values (lambda () expression)
	   (lambda (identifier identifiers ... . _)
	     body + ...)))

      ((_ ((structure structures ... expression)) body + ...)
       #'(call-with-values (lambda () expression)
	   (match-lambda* 
	       ((structure structures ... . _) body + ...)
	     (_ (error 'named-match-let-values 
		       (current-source-location)
		       'name)))))

      ((_ name ((identifier identifiers ... expression) body + ...))
       (and (identifier? #'name)
	    (every identifier? #'(identifier identifiers ...)))
       #'(let ((name (lambda (identifier identifiers ...) body + ...)))
	   (call-with-values (lambda () expression) name)))

      ((_ name ((structure structures ... expression) body + ...))
       (identifier? #'name)
       #'(let ((name (match-lambda* ((structure structures ...) body + ...)
		       (_ (error 'named-match-let-values
				 (current-source-location)
				 'name)))))
	   (call-with-values (lambda () expression) name)))

      ;; it should generally be discouraged to use the plain let
      ;; with multiple values, because there's no natural way to implement
      ;; that when there's more than one (multiple-value) binding,
      ;; but it could be added for completeness
#|
      ((_ ((structure structures ... expression) ...)
	  body + ...)
       #'(match-let/error (((structure structures ... . _) 
			    (list<-values expression)) ...)
			  body + ...))
      
      ((_ name ((structure structures ... expression) ...)
	  body + ...)
       (identifier? #'name)
       #'(letrec ((loop 
		   (match-lambda* 
		       (((structure structures ... . _) ...)
			(let-syntax ((name (syntax-rules ()
					     ((_ args (... ...))
					      (loop (list<-values args)
						    (... ...))))))
			  body + ...))
		     (_ (error 'named-match-let-values 
			       (current-source-location)
			       'name)))))
		  (loop (list<-values expression) ...)))
|#
      )))

(define-syntax match-let*-values
  (lambda (stx)
    (syntax-case stx ()

      ((_ ((identifier expression) ...) ;; optimization: regular let*
	  body + ...)
       (every identifier? #'(identifier ...))
       #'(let* ((identifier expression) ...)
	   body + ...))
      
      ((_ ((identifier expression) remaining-bindings ...)
	  body + ...)
       (identifier? #'identifier)
       #'(let ((identifier expression))
	   (match-let*-values (remaining-bindings ...) body + ...)))

      ((_ ((structure expression) remaining-bindings ...)
	  body + ...)
       #'(match-let/error ((structure expression))
			  (match-let*-values (remaining-bindings ...) 
					     body + ...)))

      ((_ ((identifier identifiers ... expression) remaining-bindings ...)
	  body + ...)
       (every identifier? #'(identifier identifiers ...))
       #'(call-with-values (lambda () expression) 
	   (lambda (identifier identifiers ... . _)
	     (match-let*-values (remaining-bindings ...) 
				body + ...))))

      ((_ ((structure structures ... expression) remaining-bindings ...)
	  body + ...)
       #'(call-with-values (lambda () expression) 
	   (match-lambda* ((structure structures ... . _)
			   (match-let*-values (remaining-bindings ...) 
					      body + ...))
	     (_ (error 'match-let*-values (current-source-location))))))
      )))

(define-syntax and-let*/match
  (lambda (stx)
    (syntax-case stx ()

      ((_)
       #'#t)

      ((_ ())
       #'#t)

      ((_ () body ...)
       #'(let () body ...))

      ((_ ((value binding) rest ...) body ...)
       (identifier? #'value)
       #'(let ((value binding))
	   (and value
		(and-let*/match (rest ...)
				body ...))))

      ((_ ((value binding) rest ...) body ...)
       #'(match binding
	   (value
	    (and-let*/match (rest ...)
	      body ...))
	   (_ #f)))

      ((_ ((condition) rest ...)
	  body ...)
       #'(and condition
	      (and-let*/match (rest ...)
		body ...)))

      ((_ ((values ... expression) rest ...) body ...)
       (every identifier? #'(values ...))
       #'(call-with-values (lambda () expression)
	   (match-lambda* 
	       ((values ... . _)
		(and values ...
		     (and-let*/match (rest ...)
				     body ...)))
	     (_ #f))))

      ;; this behavior can be questionable, but to increase coherence,
      ;; every identifier bound with multiple values at the top level
      ;; must be non-false, so while
      ;;
      ;;    (and-let* ((a b #f (values 1 2 #f))) #t)
      ;;
      ;; will succeed, 
      ;;
      ;;    (and-let* ((a b #f (values 1 #f #f))) #t)
      ;;
      ;; will fail.
      ;; On the other hand, arguments bound as a result to pattern-matching
      ;; can have any value, so 
      ;;
      ;; (and-let* (((a) (b) (values '(#f) '(#f)))) #t)
      ;;
      ;; will succeed.
      ((_ ((values ... expression) rest ...) body ...)
       (with-syntax (((identifiers ...) (filter identifier? #'(values ...))))
	 #'(call-with-values (lambda () expression)
	     (lambda args
	       (match args
		 ((values ... . _)
		  (and identifiers ...
		       (and-let*/match (rest ...)
				       body ...)))
		 (_ #f))))))
      )))
