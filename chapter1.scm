; Exercise 1.3
(DEFINE (LSS x y z)
	(DEFINE (SQUARE k) (* k k))
	(DEFINE (SOS n1 n2) (+ (SQUARE n1) (SQUARE n2)))
	(COND ((AND (> x z) (> y z)) (SOS x y))
	      ((AND (> y x) (> z x)) (SOS z y))
	      (ELSE (SOS x z))))


; Exercise 1.4
(define (a-plus-abs-b a b)
	((if (> b 0) + -) a b))
; substitution model states that the operator must be interpreted as first thing 
; b > 0 ==> (+ a b)
; b <= 0 ==> (- a b)

; Exercise 1.5
(define (p) (p))

(define (test x y)
  (if (= x 0)
    0
    y))

(test 0 (p))
; APPLICATIVE ORDER --> (p) will be evaluated immediately, entering an infinite recursion
; NORMAL ORDER --> (if (= 0 0) 0 (p)) --> 0 finite result
; NOTE: the mit-scheme interpreter uses the applicative-order evaluation !!!

; Exercise 1.8
(define (cube-root-iter guess x)
  (define (cube n) (* n n n))
  (define (good-enough? guess x)
    (< (abs (- (cube guess) x)) 0.001))
  (define (mod-avg guess x)
    (/ (+ (* 2 guess) (/ x (square guess))) 3))
  (if  (good-enough? guess x)
       guess
       (cube-root-iter (mod-avg guess x) x)))

(define (croot x)
  (cube-root-iter 1.0 x))


; Exercise 1.10 -- Ackerman's function
(define (A x y)
  (cond ((= y 0) 0)
	((= x 0) (* 2 y))
	((= y 1) 2)
	(else (A (- x 1)
		 (A x (- y 1))))))

; Exercise 1.11
; f(n) = n if n < 3
; f(n) = f(n-1) + 2f(n-2) + 3f(n-3) if n >=3

(define (recursive-f n)
  (if (< n 3)
      n
      (+ (recursive-f (- n 1)) (* 2 (recursive-f (- n 2))) (* 3 (recursive-f (- n 3))))))

(define (iterative-f n)
  (define (comb x y z)
    (+ (* 3 z) (* 2 y) x))
  (define (iter a1 a2 a3 counter)
    (if (> counter n)
	a1
	(iter (comb a1 a2 a3) a1 a2 (+ counter 1))))
    (if (< n 3)
      n
      (iter 2 1 0 3))) 

(define (compute-function n)
  (if (< n 3)
      n
      (iterative-f n)))


; Exercise 1.12
; create a Pascal's triangle
; elements are like in matrix p[i,j]
;;;1
;;;1  1 
;;;1  2  1 
;;;1  3  3  1 
;;;1  4  6  4  1 
;;;1  5  10 10 5  1
(define (pascal row column) 
  (cond ((= column 0) 1)
	((= column row) 1)
	(else (+ (pascal (- row 1) (- column 1)) (pascal (- row 1) column)))))


; Exercise 1.15
; the values of the angle decrease by a 1/3 factor each iteration
; this means that the complexity of the alg is O(logN) in time and space
(define (sine angle)
  (define (cube x) (* x x x))
  (define (p x) (- (* 3 x) (* 4 (cube x))))
  (if (not (> (abs angle) 0.1))
      angle
      (p (sine (/ angle 3.0)))))

; Exercise 1.16 
; make the following procedure iterative
(define (fast-expt b n)
  (cond ((= n 0) 1)
	((even? n) (square (fast-expt b (/ n 2))))
	(else (* b (fast-expt b (- n 1))))))

; keep in mind that b^{2n} = (b^2)^n
; any even exponent can be "rewritten" using the expression above without actually computing it
; it is just reduced to a square (the accumulator a does not change in these iterations)
(define (fast-exp-iter b n a)
  (cond ((= n 0) a)
	((even? n) (fast-exp-iter (square b) (/ n 2) a))
	(else (fast-exp-iter b (- n 1) (* a b)))))

; Exercise 1.17
; multiplications by means of repeated additions
; define a multiplication in log number steps (recursive process)
(define (mul a b)
  (if (or (= b 0) (= a 0))
      0
      (+ a (mul a (- b 1))))))

(define (double n) (* n 2))
(define (halve n) (/ n 2))

(define (fast-mul n b)
  (cond ((or (= b 0) (= n 0)) 0)
	((even? b) (double (fast-mul n (halve b))))
	(else (+ n (fast-mul n (- b 1))))))

; Exercise 1.18
; Repeat previous exercise -- iterative process
; b odd --> n*b = n + n*(b-1)
; b even --> n*b = (2*n)*(n/2) [no change]
; acc starts from 0
(define (fast-mul-iter n b acc)
  (cond ((or (= b 0) (= n 0)) acc)
	((even? b) (fast-mul-iter (double n) (halve b) acc))
	(else (fast-mul-iter n (- b 1) (+ acc n)))))

; Exercise 1.19
; you can find it by using a simple substitution
; q' = 2*p*q + q^2
; p' = q^2 + p^2
(define (fib n) 
   (fib-iter 1 0 0 1 n)) 
 (define (fib-iter a b p q count) 
   (cond ((= count 0) b) 
         ((even? count) 
          (fib-iter a 
                    b 
                    (+ (square p) (square q)) 
                    (+ (* 2 p q) (square q)) 
                    (/ count 2))) 
         (else (fib-iter (+ (* b q) (* a q) (* a p)) 
                         (+ (* b p) (* a q)) 
                         p 
                         q 
                         (- count 1)))))

; Exercise 1.20
; use normal order evaluation for (gcd 206 40)
; interpret IF as in Exercise 1.5 (i.e. predicate evaluated first)
(define (gcd a b)
  (if (= b 0)
      a
      (gcd b (remainder a b))))

; (gcd 206 40) NORMAL ORDER EVALUATION
; b=40 --> (gcd 40 (remainder 206 40))
; b=6  --> (gcd (remainder 206 40) (remainder 40 (remainder 206 40)))
; b=4  --> (gcd (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40))))
; b=2  --> (gcd (remainder (remainder 206 40) (remainder 40 (remainder 206 40))) (remainder (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))))
; b=0 --> (remainder (remainder 206 40) (remainder 40 (remainder 206 40))
; remainder executed 26 times (+ 4 times for the predicate evaluations)

; (gcd 206 40) APPLICATIVE ORDER EVALUATION
; b=40 --> (gcd 40 (remainder 206 40)) --> (gcd 40 6)
; b=6  --> (gcd 40 6) --> (gcd 6 (remainder 40 6)) --> (gcd 6 4)
; b=4  --> (gcd 6 4) --> (gcd 4 (remainder 6 4)) --> (gcd 4 2)
; b=2  --> (gcd 4 2) --> (gcd 2 (remainder 4 2)) --> (gcd 2 0)
; b=0  --> 2
; reminder executed 4 times

; Exercise 1.21

(define (devides? a b)
  (= (remainder b a) 0))

(define (find-divisor n test-divisor)
  (cond ((> (square test-divisor) n) n)
	((devides? test-divisor n) test-divisor)
	(else (find-divisor n (+ test-divisor 1)))))

(define (smallest-divisor n)
  (find-divisor n 2))

; (smallest-divisor 199) 
; (find-divisor 199 2)
; ... 199 is prime

; (smallest-divisor 19999) --> not prime
; (find-divisor 19999 2)
; (find-divisor 19999 3)  
; (find-divisor 19999 4)  
; (find-divisor 19999 5)  
; (find-divisor 19999 6)  
; (find-divisor 19999 7) --> 7

; Exercise 1.22
; write a procedure to search for 3 primes larger than 1k, 10k, 1M
(define (prime? n)
  (= n (smallest-divisor n)))

(define (timed-prime-test n)
  (newline)
  (display n)
  (start-prime-test n (runtime)))

(define (start-prime-test n start-time)
  (if (prime? n)
      (report-prime (- (runtime) start-time))))

(define (report-prime elapsed-time)
  (display " *** ")
  (display elapsed-time))

(define (find-primes-bigger base upper)
  (define (iter n)
    (cond ((<= n upper) 
	   (timed-prime-test n)
	   (iter (+ n 2)))))
    (iter (if (odd? base) base (+ base 1)))))

; Exercise 1.23
; rewrite test-divisor to avoid all the multiples of 2
; define procedure (next n) that returns 3 if n=2, return n+2 otherwise 
; The observed ratio of the speed of the two algorithms is not 2, but roughly 1.5 (or 3:2).
; This is mainly due to the NEXT procedure's IF test.
; The input did halve indeed, but we need to do an extra IF test.
(define (devides? a b)
  (= (remainder b a) 0))

(define (next n)
  (if (= n 2)
      3
      (+ n 2)))

(define (find-divisor n test-divisor)
  (cond ((> (square test-divisor) n) n)
        ((devides? test-divisor n) test-divisor)
        (else (find-divisor n (next test-divisor)))))

(define (smallest-divisor n)
  (find-divisor n 2))

(define (prime? n)
  (= n (smallest-divisor n)))

(define (timed-prime-test n)
  (newline)
  (display n)
  (start-prime-test n (runtime)))

(define (start-prime-test n start-time)
  (if (prime? n)
      (report-prime (- (runtime) start-time))))

(define (report-prime elapsed-time)
  (display " *** ")
  (display elapsed-time))

; Exercise 1.24
; modify timed-prime-test in exercise 1.22 to use fast-prime
; we will use Fermat's Little Thorem [ignorin Carmichael numbers]
; T: if n is a prime number and a is any ositive integer less than n
; then a^n mod n = a mod n

; exponential modulo n
; exp even --> (base)^exp mod n = (base^(exp/2))^2 mod n
; exp odd  --> (base)^exp mod n = [base * (base)^(exp-1)] mod n
(define (expmod base exp m) 
   (cond ((= exp 0) 1) 
         ((even? exp) 
          (remainder (square (expmod base (/ exp 2) m)) 
                     m)) 
         (else 
          (remainder (* base (expmod base (- exp 1) m)) 
                     m))))  

; fermat test
; chose a random numbeteen 1 and (n-1) inclusive and check Fermat little theorem
; NOTE: (random m) returns a value between 0 and (m-1) so we need to add +1 to the result
; REMEMBER: fermat's little theorem is necessary but not sufficient for primality
(define (fermat-test n)
  (define (try-it a)
    (= (expmod a n n) a))
  (try-it (+ 1 (random (- n 1)))))

; run the fermat-test a defined number of times
(define (fast-prime? n times)
  (cond ((= times 0) #t)
	((fermat-test n) (fast-prime? n (- times 1))) ; repeat procedure 
	(else #f))) ; not passed fermat test

(define (prime? n)
  (fast-prime? n 100))

(define (timed-prime-test n)
  (newline)
  (display n)
  (start-prime-test n (runtime)))

(define (start-prime-test n start-time)
  (if (prime? n)
      (report-prime (- (runtime) start-time))))

(define (report-prime elapsed-time)
  (display " *** ")
  (display elapsed-time))

; Exercise 1.25
; is the following procedure any good for the fast prime tester?
(define (expmod base exp m)
  (remainder (fast-expt base exp) m))
; this would work, but the procedure would be forced to handle big numbers
; there is an unnecessary risk for overflow
; executing the modulus operation keeps numbers between 0 and (m-1) as a value

; Exercise 1.26
; why is the following procedure O(n) and not O(logn)?

(define (expmod base exp m)
  (cond ((= exp 0) 1)
	((even? exp)
	 (reminder (* (expmod base (/ exp 2) m) ; the problem is here as the 2 expmod are both computed
		      (expmod base (/ exp 2) m)); this is an effect of the substitution model
		   m))
	(else
	  (remainder (* base (expmod base (- exp 1) m))
		     m))))
; basically, computing (expmod base (/ exp 2) m) twice, we are nullifying
; the temporal effect of the division
; this generates a TREE recursion instead of a linear recursion !!!
; depth L=log(n) with number of nodes Sum 2^i for i=0..L = 2^(L+1)-1
; this means that the number of steps is O(2^L) ~ O(n)
;             *
;            /  \
;           *    * 
;          / \   / \
;         *   *  *  *

; Exercise 1.27 
; Write a procedure that executes Fermat's Little Theorem for each number a < n
; try for n Carmichal number [561, 1105, 1729, 2465, 2821, 6601]

(define (fermat-test n a)
  (= (expmod a n n) a))

; run the fermat-test a defined number of times
(define (carmichael-test n a)
  (cond ((or (= n 0) (= n 1)) #f) ; 0 and 1 are not prime/carmichael by definition
    	((= (- n a) 0) #t)
	((fermat-test n a) (fast-prime? n (+ a 1))) ; repeat procedure 
	(else #f))) ; not passed fermat test

(define (carmichael? n)
  (carmichael-test n 1))

; Exercise 1.28
; to review later !!! 

; Exercise 1.29
 (define (sum term a next b) 
   (if (> a b) 
       0 
       (+ (term a) 
          (sum term (next a) next b)))) 

(define (simps f a b n)
  (define h (/ (- b a) n))
  (define (next-t x) (+ x 1))
  (define (aux k)
    (* (cond ((or (= k 0) (= k n)) 1)
	     ((even? k) 2)
	     ((odd? k) 4))
       (f (+ a (* k h)))))
  (* (/ h 3.0)
     (sum aux 0 next-t n)))

; Exercise 1.30
; make the sum procedure iterative [easy]
(define (sum term a next b)
  (define (iter a result)
    (if (> a b)
	result
	(iter (next a) (+ (term a) result))))
  (iter a 0))

; Exercise 1.31
; define the product procedure
; RECURSIVE PROCESS
(define (product term a next b)
  (if (> a b)
      1
      (* (term a)
	 (product term
		  (next a)
		  next
		  b))))

; ITERATIVE PROCESS
(define (product term a next b)
  (define (iter a result)
    (if (> a b)
	result
	(iter (next a) (* (term a) result))))
  (iter a 1))

; factorial using the product procedure
(define (factorial n)
  (if (or (= n 0) (= n 1))
      1
      (product (lambda (x) x) 
	       1
	       (lambda (x) (+ x 1))
	       n)))

; approximate pi using the product procedure
(define (pi-approx precision)
  (define (term-f n)
    (if (even? n) 
	(/ (+ n 2.0) (+ n 1.0)) 
	(/ (+ n 1.0) (+ n 2.0))))
  (* 4 
     (product term-f
	      1
	      (lambda (x) (+ x 1))
	      precision)))

; Exercise 1.32
; create an accumulate procedure that generalizes sum and product

; ITERATIVE PROCESS
(define (accumulate combiner null-value term a next b)
  (define (iter a result)
    (if (> a b)
        result
        (iter (next a) (combiner (term a) result))))
  (iter a null-value))

; RECURSIVE PROCESS
(define (accumulate combiner null-value term a next b)
  (if (> a b)
      null-value
      (combiner (term a) (accumulate combiner null-value term (next a) next b))))

(define (sum term a next b)
  (accumulate + 0 term a next b))
(define (product term a next b)
  (accumulate * 1 term a next b))

; Exercise 1.33
(define (filtered-accumulate combiner null-value term a next b filter)
  (define (iter a result)
    (if (> a b)
        result
        (iter (next a) (if (filter a)
			   (combiner (term a) result)
			   result))))
  (iter a null-value))


(define (filtered-accumulate combiner null-value term a next b filter)
  (if (> a b)
      null-value
      (combiner (if (filter a)
		    (term a)
		    null-value)
		(accumulate combiner null-value term (next a) next b))))

; using the prime? procedure as a filter
; sum af all the primes between a and b
(define (sum-of-prime-squares a b) (filtered-accumulate + 0 
							square 
							a 
							(lambda (x) (+ x 1)) ;; increment
							b
							prime?))

; sum of all the positive integers i < n such that GCD(i, n) = 1 [relative prime]
(define (product-of-relative-primes-upto n)
  (filtered-accumulate *
		       1
		       (lambda (x) x) ; identity
		       1
		       (lambda (x) (+ x 1)) ; increment
		       n
		       (lambda (x) (= 1 (gcd x n)))))

; Exercise 1.34
(define (f g)
  (g 2))
(f square) ; ==> 4
(f (lambda (x) (* x (+ x 1)))) ; ==> 6
(f f) ; (f f) --> (f 2) --> (2 2) nonsense combination

; Exercise 1.35
; show that the golden ratio phi is fixed point of x --> 1 + (1/x)
(define tolerance .00000001)
(define (fixed-point f first-guess)
  (define (close-enuf? v1 v2)
    (< (abs (- v1 v2)) tolerance))
  (define (try guess)
    (let ((next (f guess)))
	  (if (close-enuf? guess next)
	      next
	      (try next))))
  (try first-guess))

(define golden-ratio
  (fixed-point (lambda (x) (+ 1 (/ 1.0 x)))
	       1))

; Exercise 1.36
; alter the procedure fixed-point to show its approximations
(define tolerance .00000001)
(define (fixed-point f first-guess)
  (define (close-enuf? v1 v2)
    (< (abs (- v1 v2)) tolerance))  
  (define (try guess)
    (display " *** ")
    (display guess)
    (newline)
    (let ((next (f guess)))
          (if (close-enuf? guess next)
              next
              (try next))))
  (try first-guess))

(define equation            
  (fixed-point (lambda (x) (/ (log 1000) (log x)))          
               2))

; Exercise 1.37
; write a procedure to compute the k-term finite continued fraction
; RECURSIVE VERSION
; f(i) = N(i) / [D(i) + f(i+1)]
(define (cont-frac n d k)
  (define (recur i)
    (if (> i k)
	0
	(/ (n i) (+ (d i) (recur (+ i 1))))))
  (recur 1))

; ITERATIVE VERSION
; start from the index = k down to 0
; ans(i) = N(i) / [D(i) + ans(i+1)]
(define (cont-frac n d k)
  (define (iter i ans)
    (if (= i 0)
	ans
	(iter (- i 1)
	      (/ (n i) (+ (d i) ans)))))
  (iter k 0))

(cont-frac (lambda (i) 1.0)
	   (lambda (i) 1.0)
	   1000)



; Exercise 1.38
; compute Euler's number e by using cont-frac
(define e 
  (+ 2
     (cont-frac (lambda (i) 1.0)
           (lambda (i)
             (if (= (remainder i 3) 2)
                 (* 2 (/ (+ i 1) 3.0))
                 1))
           1000)))

(cont-frac (lambda (i) 1.0)
	   (lambda (i)
	     (if (= (remainder i 3) 2)
		 (* 2 (/ (+ i 1) 3))
		 1))
	   1000)

; Exercise 1.39
; define procedure (tan-cf x k) to compute an approximation to tan(x) with Lambert's formula
; k specifies the number of terms to compute as in Ex 1.37
; N(i) = -x^2
; D(i) = 2*i - 1 [odd number]
; result must be devided by (-x)
(define (tan-cf x k)
  (/ (cont-frac (lambda (i) (- (square x))) 
             	(lambda (i) (- (* 2.0 i) 1)) ; generate odd number
             	k)
     (- x)))

