#lang typed/racket
(require typed/rackunit)

;language definition
;language definition
(define-type ExprC (U NumC IdC StrC MutC IfC LamC SeqC AppC))
(struct NumC ([n : Real]) #:transparent)                                   
(struct IdC  ([id : Symbol]) #:transparent)                                
(struct StrC ([s : String]) #:transparent)
(struct MutC ([id : Symbol] [val : ExprC]))
(struct IfC  ([c : ExprC] [then : ExprC] [else : ExprC]) #:transparent)        
(struct LamC ([arg : (Listof Symbol)] [body : ExprC]) #:transparent)
(struct SeqC ([lst : (Listof ExprC)]))
(struct AppC ([fun : ExprC] [arg : (Listof ExprC)]) #:transparent)

;value definition
(define-type Value (U NumV BoolV StrV ClosV PrimopV ArrV NullV))
(struct NumV    ([n : Real]) #:transparent)
(struct BoolV   ([b : Boolean]) #:transparent)
(struct StrV    ([s : String]) #:transparent)
(struct ClosV   ([arg : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimopV ([op : Symbol]) #:transparent)
(struct ArrV    ([start : Real] [len : Real]) #:transparent)
(struct NullV   () #:transparent)

;types definition
(define-type Type (U NumT))
(struct NumT ())

;environment definition
(define-type Env (Listof Binding)) 
(struct Binding ([name : Symbol] [loc : Location])) 
;environment init
(define mt-env '())
(define extend-env cons)
(define top-env (list
                 (Binding 'error 14)
                 (Binding 'false 13)
                 (Binding 'true 12)
                 (Binding 'alen 11)
                 (Binding 'aset 10)
                 (Binding 'aref 9)
                 (Binding 'arr 8)
                 (Binding 'arr-eq? 7)
                 (Binding 'str-eq? 6)
                 (Binding 'num-eq? 5)
                 (Binding '<= 4)
                 (Binding '/ 3)
                 (Binding '* 2)
                 (Binding '- 1)
                 (Binding '+ 0)))


(define-type-alias Location Real)
(struct Store ([next : Natural] [cells : (Listof Cell)]) #:transparent)
(struct Cell ([loc : Location] [val : Value]) #:transparent)
(struct Result ([val : Value] [store : Store]) #:transparent)


(define top-store (Store 15 
                         (list
                          (Cell 14 (PrimopV 'error))
                          (Cell 13 (BoolV #f))
                          (Cell 12 (BoolV #t))
                          (Cell 11 (PrimopV 'alen))
                          (Cell 10 (PrimopV 'aset))
                          (Cell 9 (PrimopV 'aref))
                          (Cell 8 (PrimopV 'arr))
                          (Cell 7 (PrimopV 'arr-eq?))
                          (Cell 6 (PrimopV 'str-eq?))
                          (Cell 5 (PrimopV 'num-eq?))
                          (Cell 4 (PrimopV '<=))
                          (Cell 3 (PrimopV '/))
                          (Cell 2 (PrimopV '*))
                          (Cell 1 (PrimopV '-))
                          (Cell 0 (PrimopV '+)))))

(define extend-store cons)

(define (print-store [store : Store]) : Void
  (printf "Store (next: ~a)\n" (Store-next store))
  (for-each (lambda ([cell : Cell])
              (printf "  Cell (loc: ~a, val: ~a)\n" (Cell-loc cell) (Cell-val cell)))
            (Store-cells store)))


;TOP-INTERP
;in: list of oazo5 syntax functions fun-sexps
;out: the evaluation of main function in fun-sexps
(define (top-interp [s : Sexp]) : String
  (serialize (Result-val (interp (parse s) top-env top-store))))


;;TOP-INTERP FOR PRINTING STORE
;in: list of oazo5 syntax functions fun-sexps
;out: the evaluation of main function in fun-sexps
#;(define (top-interp [s : Sexp]) : Void
    (print-store (Result-store (interp (parse s) top-env top-store))))
  


;SERIALIZE
;in: a Value from interp
;out: the string representation of that value
(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (number->string n)]
    [(BoolV #t) "true"]
    [(BoolV #f) "false"]
    [(StrV val) (format "~v" val)]
    [(ClosV _ _ _) "#<procedure>"]
    [(PrimopV _) "#<primop>"]
    [(NullV)  "#<void>"]
    [(ArrV _ _) "#array"]))




;INTERP
;in: ExprC exp, list of FundefC lst
;out: evaluation of exp as a Real
(define (interp [exp : ExprC] [env : Env] [store : Store]) : Result 
  (match exp
    [(NumC n) (Result (NumV n) store)]
    [(StrC s) (Result (StrV s) store)]
    [(MutC id val)
     (define interped-result (interp val env store))
     (define new-store (Result-store interped-result))
     (define new-val (Result-val interped-result))
     (define newcell (Cell (lookup-loc id env) new-val))
     (Result (NullV) (Store (Store-next store) (cons newcell (Store-cells store))))]
    
    [(IdC id) (Result (lookup id env store) store)] 
    [(LamC args body) (Result (ClosV args body env) store)]
    [(SeqC args) (last (thread args env store))]
    [(IfC if then else) (define if_interped (interp if env store))
                        (match (Result-val if_interped)
                          [(BoolV b) 
                           (cond [b (interp then env (Result-store if_interped))]
                                 [else (interp else env (Result-store if_interped))])]
                          [else (error 'interp "OAZO5 if must be a truth value")])]
    [(AppC fun (list args ...)) (define f (interp fun env store))
                                #;(define arguments (map (lambda ([a : ExprC])
                                                           (Result-val (interp a env store))) args))
                                (define result-arguments (thread args env (Result-store f)))
                                (define last-store (Result-store (last result-arguments)))
                                (define arguments (get-vals result-arguments))
                                (match (Result-val f)
                                  [(PrimopV op) (operation op arguments last-store)] #;(WHERE DO STORE STORE? --> LOSING INNER STORE AFTER RETURN FROM ARR)
                                  #;[else (error 'interp "unimplemented appC")]
                                  [(ClosV (list args ...) body env)
                                   (cond [(= (length arguments) (length args))
                                          (define new-env-store (extend arguments args last-store env)) 
                                            
                                          (interp body (car new-env-store) (cdr new-env-store))]
                                         [else (error 'interp "OAZO5 incorrect argument length")])]
                                  [(NumV n) (error 'interp "OAZO5 incorrect argument type of ~v" n)])]  
    [else (error 'interp "unimplemented")])) 

;EXTEND 
;in: a list or agumenets, list of parameters, and current environment
;out: the new environment that has the parameters with the values of arguments
#;(define (extend [arg : (Listof Value)] [param : (Listof Symbol)] [env : Env]) : Env
    (match arg
      ['() env]
      [a (extend (rest arg) (rest param) (extend-env (Binding (first param) (first arg)) env))]))
;EXTEND
(define (extend [arg : (Listof Value)] [param : (Listof Symbol)] [store : Store] [env : Env]) : (Pairof Env Store)
  (cons (extend-e param (Store-next store) env) (extend-s arg store))
  )
;EXTEND-ENVIRONMENT
(define (extend-e [param : (Listof Symbol)] [num : Real] [env : Env]) : Env 
  (match param
    ['() env]
    [p (cons (Binding (first param) num) (extend-e (rest param) (+ num 1) env))]))
;EXTEND-STORE
(define (extend-s [arg : (Listof Value)] [store : Store]) : Store
  (match arg
    ['() store]
    [a (Store (+ (Store-next store) 1) (cons (Cell (Store-next store) (first arg)) (Store-cells store)))]))

#;(CREATE NEW CELL IN STORE WITH STORE-NEXT AND INTERPED ARG (FIRST ARGUMENTS))
#;(CREATE NEW BINDING IN ENV WITH STORE-NEXT AND SYMBOL (FIRST ARG))
 
;;THREAD
(define (thread [args : (Listof ExprC)] [env : Env] [store : Store]) : (Listof Result)
  (match args
    ['() '()]
    [(cons f r)
     (match (interp f env store)
       [(Result v s) (cons (Result v s) (thread r env s))])]))


;;GET-VALS
(define (get-vals [results : (Listof Result)]) :  (Listof Value) 
  (match results
    ['() '()]
    [(cons f r) (cons (Result-val f) (get-vals r))]))

 
;LOOKUP-LOCATION
(define (lookup-loc [for : Symbol] [env : Env]) : Real
  (match env
    ['() (error 'lookup "OAZO5 name not found: ~e" for)]
    [(cons (Binding name loc) r) (cond
                                   [(equal? name for) loc]
                                   [else (lookup-loc for r)])]))

;LOOKUP
;in: a symbol and the current environment
;returns the symbols value in the environment, erros if not found
(define (lookup [for : Symbol] [env : Env] [store : Store]) : Value
  (match env
    ['() (error 'lookup "OAZO5 name not found: ~e" for)]
    [(cons (Binding name loc) r) (cond
                                   [(equal? name for) (fetch loc store)]
                                   [else (lookup for r store)])]))

;FETCH
(define (fetch [loc : Location] [store : Store]) : Value
  (match (Store-cells store)
    ['() (error 'lookup "OAZO5 location not found: ~e" loc)]
    [(cons (Cell location op) r) (cond
                                   [(equal? location loc) op]
                                   [else (fetch loc (Store (Store-next store) r))])]))


 
;OPERATION
;in: the operation as a symbol and the two values
;out: values applied to the racket operation based on that symbol
(define (operation [op : Symbol] [args : (Listof Value)] [store : Store]) : Result
  (cond
    [(equal? (length args) 1)
     (match op
       ['alen (Result (NumV (ArrV-len (cast (first args) ArrV))) store)]
       ['error (error 'oazo7 "user-error")]
       [other (error 'operation "OAZO7 bad syntax")])]
    [(equal? (length args) 2) (define l (first args))
                              (define r (first (rest args)))
                              (cond [(and (NumV? l) (NumV? r))
                                     (match op
                                       ['+ (Result (NumV (+ (NumV-n l) (NumV-n r))) store)]
                                       ['- (Result (NumV (- (NumV-n l) (NumV-n r))) store)]
                                       ['* (Result (NumV (* (NumV-n l) (NumV-n r))) store)]
                                       ['/ (cond [(equal? (NumV-n r) 0) (error 'operation "OAZO5 div by 0")]
                                                 [else (Result (NumV (/ (NumV-n l) (NumV-n r))) store)])]
                                       ['<= (Result (BoolV (<= (NumV-n l) (NumV-n r))) store)]
                                       ['num-eq? (Result (BoolV (equal? (NumV-n l) (NumV-n r))) store)]
                                       ['arr
                                        (define len (NumV-n l))
                                        (define start (Store-next store))
                                        (define new-store (create-arr store r len))
                                        (Result (ArrV start len) new-store)])]
                                    [(and (StrV? l) (StrV? r))
                                     (match op
                                       ['str-eq? (Result (BoolV (equal? (StrV-s l) (StrV-s r))) store)])]
                                    [(and (ArrV? l) (ArrV? r))
                                     (match op
                                       ['arr-eq? (Result (BoolV (and (equal? (ArrV-start l) (ArrV-start r))
                                                                     (equal? (ArrV-len l) (ArrV-len r)))) store)])]
                                    [(and (ArrV? l) (NumV? r))
                                     
                                     (print args)
                                     (match op
                                       ['aref (cond [(<= (NumV-n r) (ArrV-len l)) (Result (fetch (+ (ArrV-start l) (NumV-n r)) store) store)]
                                                    [else (error 'operation "OAZO7 Array indexing out of bounds") ])])]
                                    [else (error 'opertion "OAZO7 invalid operation")])] 
    [(equal? (length args) 3)
     (match op
       ['aset (define arr (cast (first args) ArrV))
              (define arr-idx (NumV-n (cast (first (rest args)) NumV))) 
              (define idx (NumV (+ arr-idx (ArrV-start arr))))
              (define newval (first (rest (rest args))))
              (define newcell (Cell (NumV-n idx) newval))
              (define new-store (cons newcell (Store-cells store)))
              
              (Result (NullV) (Store (Store-next store) new-store))])]
    [else (error 'operation "OAZO7 operation not valid")]))


#;(define (mut-arr! [idx : NumV] [newval : NumV] [lst : (Listof Cell)]) : (Listof Cell)
    (match lst
      ['() '()]
      [(cons f r) (cond [(equal? (Cell-loc f) idx) (cons (Cell (NumV-n idx) newval) (mut-arr! idx newval r))]
                        [else (cons f (mut-arr! idx newval r))])]))



;;CREATE-ARR
(define (create-arr [store : Store] [val : Value] [size : Real]) : Store
  (cond [(equal? 0 size) store]
        [(create-arr (cdr (allocate store val)) val (- size 1))]))



;;ALLOCATE
(define (allocate [store : Store] [val : Value]) : (Pairof Location Store)
  (define base (Store-next store))
  (cons base (Store (+ base 1) (cons (Cell base val) (Store-cells store)))))

 
 

;PARSE
;in: s-expression code
;out: the parsed ExprC representation of code
(define (parse [code : Sexp]) : ExprC
  (match code 
    [(? real? n)   (NumC n)]
    [(? string? s) (StrC s)]
    [(list (? symbol? s) ':= e) (MutC s (parse e))]
    [(list 'if i 'then t 'else e) (IfC (parse i) (parse t) (parse e))]
    [(list 'let (list (? symbol? (? is-allowed? var)) '<- val) ... body)
     (parse (cast (cons (list 'anon var ': body) val) Sexp))]
    [(? symbol? s) (cond [(is-allowed? s) (IdC s)]
                         [else (error 'parse "OAZO5 keyword error: ~e" s)])]
    [(list 'anon (list (? symbol? (? is-allowed? args)) ...) ': body)
     (cond [(and (not-has-duplicates? (cast args (Listof Symbol)))
                 (cast args (Listof Symbol))) (LamC (cast args (Listof Symbol)) (parse body))]
           [else (error 'interp "OAZO5 two args with the same name")])]
    [(list 'seq args ...) (SeqC (for/list ([item (in-list args)]) 
                                  (parse (cast item Sexp))))]
    [(list func args ...) (AppC (parse func) (for/list ([item (in-list args)]) 
                                               (parse (cast item Sexp))))]
    [other (error 'parse "OAZO5 syntax error in ~e" other)]))





;IS-ALLOWED
;in: symbol s
;out: boolean represntation of if the symbol is not a keyword
(define (is-allowed? [s : Sexp]) : Boolean
  (match s
    ['if #f]
    ['let #f]
    ['then #f]
    ['anon #f]
    [': #f]
    ['<- #f]
    [else #t]))





;HAS-NOT-DUPLICATES
;in: a list of symbols
;out: not (boolean reprentation of if the symbol contains duplicates)
(define (not-has-duplicates? [lst : (Listof Symbol)]) : Boolean
  (define sorted-list : (Listof Symbol)
    (sort lst symbol<?)) ; Sort the list in ascending order
  (define (check-duplicates [lst : (Listof Symbol)]) : Boolean
    (cond
      [(or (empty? lst) (empty? (rest lst))) #t] ; Base case: no duplicates found
      [(equal? (first lst) (second lst)) #f] ; Found a duplicate
      [else (check-duplicates (rest lst))])) ; Recur with the rest of the list
  (check-duplicates sorted-list))

 





;------------------------ TESTING ----------------------------------
;basic functions

(check-equal? (top-interp '{+ 1 2}) "3")
(check-equal? (top-interp '{+ 1 {+ 1 2}}) "4")



#|
(check-equal? (top-interp '{let [w <- 5] [x <- 7] [y <- 5] [z <- 7] {/ {- {* {+ x y} z} w} 1}}) "79")
(check-equal? (top-interp '{{anon {x} : {+ x 1}} 8}) "9")
(check-equal? (top-interp '{{anon {x} : {<= x 9}} 8}) "true")
(check-equal? (top-interp '{{anon {x} : {<= x 9}} 80}) "false")
(check-equal? (top-interp '{{anon {h} : {h 8}} {anon {x} : {+ x 1}}}) "9") 
(check-equal? (top-interp '{{{anon {f g} : {anon {x} : {f {g x}}}} {anon {x} : {+ x 10}}
                                                                   {anon {x} : {* x 2}}} 10}) "30") 
(check-equal? (top-interp '{{anon {x} : {if {<= x 9} then {- 1 2} else {+ 1 2}}} -1}) "-1")
(check-equal? (top-interp '{let
                               {z <- {+ 9 14}}
                             {y <- 98} 
                             {p <- 44}
                             {- {+ z y} p}}) "77")
(check-equal? (top-interp '{{anon {x} : {if {equal? x "hello"} then {- 1 1} else {+ 1 2}}} "hello"}) "0")
(check-equal? (top-interp '{{anon {x} : {if {equal? x 2} then {- 1 1} else {+ 1 2}}} 1}) "3")
(check-equal? (top-interp '{{anon {x} : {if {equal? x "hello"} then {- 1 1} else {+ 1 2}}} "yes"}) "3")
(check-equal? (top-interp '{{anon {x} : {if {equal? x "hello"} then "yes" else {+ 1 2}}} "hello"})  "\"yes\"")
(check-equal? (serialize (ClosV '(x y) (NumC 0) mt-env)) "#<procedure>")
(check-equal? (serialize (PrimopV '-)) "#<primop>")
(check-equal? (parse "hello") (StrC "hello"))

;error testing
(check-exn #rx"name not found" (lambda () (top-interp '{{anon {x} : {<= y 9}} 8})))
(check-exn #rx"argument length" (lambda () (top-interp '{{anon {x y} : {<= y 9}} 8})))
(check-exn #rx"syntax" (lambda () (top-interp '{})))
(check-exn #rx"keyword" (lambda () (top-interp '{{anon {if y} : {<= y 9}} 8})))
(check-exn #rx"keyword" (lambda () (parse ':)))
(check-exn #rx"keyword" (lambda () (top-interp '{{anon {let y} : {<= y 9}} 8})))
(check-exn #rx"keyword" (lambda () (top-interp '{{anon {anon y} : {<= y 9}} 8})))
(check-exn #rx"keyword" (lambda () (top-interp '{{anon {: y} : {<= y 9}} 8})))
(check-exn #rx"keyword" (lambda () (top-interp '{{anon {<- y} : {<= y 9}} 8})))
(check-exn #rx"OAZO" (lambda () (top-interp '(+ + +))))
(check-exn #rx"keyword" (lambda () (top-interp '(+ then 4))))
(check-exn #rx"truth" (lambda () (top-interp '{{anon {x} : {if {+ 1 2} then {- 1 2} else {+ 1 2}}} -1})))
(check-exn #rx"div" (lambda () (top-interp '(/ 1 (- 3 3)))))
(check-exn #rx"OAZO" (lambda () (parse '(anon (x x) : 3)))) 
(check-exn #rx"OAZO" (lambda () (parse '(anon (x x) : 3))))
(check-exn #rx"user-error" (lambda () (top-interp '{{anon {x} : {error "whats going on"}} 8}))) 
(check-exn #rx"user-error" (lambda () (top-interp '(+ 4 (error "1234")))))
(check-exn #rx"user-error" (lambda () (top-interp '((anon (e) : (e e)) error))))
(check-exn #rx"OAZO5 incorrect argument type of" (lambda () (top-interp '{3 4 5})))

|#



