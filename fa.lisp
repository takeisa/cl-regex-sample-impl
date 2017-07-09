;;
;; Regular Expression Library Sample Implementaion
;;
;; Author: Satoshi Takei
;;

;; --------------------
;; FA
;; --------------------

(defun make-fa-rule (state char next-state)
  (list state char next-state))

(defun fa-rule-state (rule)
  (car rule))

(defun fa-rule-char (rule)
  (cadr rule))

(defun fa-rule-next-state (rule)
  (caddr rule))

(defun make-fa-design (rules accept-states)
  (list rules accept-states))

(defun fa-design-rules (design)
  (car design))

(defun fa-design-accept-states (design)
  (cadr design))

(defun fa-design-start-state (design)
  (let ((first-rule (car (fa-design-rules design))))
    (fa-rule-state first-rule)))

(defun accept-state-p (states accept-states)
  (intersection states accept-states))

;; --------------------
;; DFA
;; --------------------

(defun make-dfa-rules (&rest rules)
  rules)

(defun dfa-next-state (rules state char)
  (flet ((rule-for () (find-if
		       #'(lambda (rule)
			   (and (equal (fa-rule-state rule) state)
				(equal (fa-rule-char rule) char)))
		       rules)))
    (let ((rule (rule-for)))
      (when (null rule)
	(error "rule not found: state=~a char=~a" state char))
      (fa-rule-next-state rule))))

(defun dfa-read-chars (rules chars)
  (reduce
   #'(lambda (state char)
       (dfa-next-state rules state char))
   chars
   :initial-value 1))

(defun dfa-accept-p (rules accept-states chars)
  (accept-state-p
   (list (dfa-read-chars rules chars))
   accept-states))

(defparameter *dfa-rules*
	      (make-dfa-rules
	       (make-fa-rule 1 #\a 2) (make-fa-rule 1 #\b 2)
	       (make-fa-rule 2 #\a 2) (make-fa-rule 2 #\b 3)
	       (make-fa-rule 3 #\a 3) (make-fa-rule 3 #\b 3)))

;; --------------------
;; NFA
;; --------------------

(defun make-nfa-rules (&rest rules)
  rules)

(defun nfa-state-next-states (rules state char)
  (mapcar #'fa-rule-next-state
	  (remove-if-not
	   #'(lambda (rule)
	       (and (equal (fa-rule-state rule) state)
		    (equal (fa-rule-char rule) char)))
	   rules)))

(defun nfa-states-next-states (rules states char)
  (remove-duplicates
   (mapcan
    #'(lambda (state) (nfa-state-next-states rules state char))
    states)))

(defun nfa-states-follow-e-transition (rules states)
  (let ((more-states (nfa-states-next-states rules states nil)))
    (if (subsetp more-states states)
	states
	(nfa-states-follow-e-transition rules (union states more-states)))))

(defun nfa-read-chars (rules chars start-state)
  (reduce
   #'(lambda (states char)
       (let ((next-states
	      (nfa-states-follow-e-transition rules
	       (nfa-states-next-states rules states char))))
	 (format t "~a -> ~a~%" states next-states)
	 next-states))
   chars
   :initial-value (nfa-states-follow-e-transition rules (list start-state))))

(defun nfa-accept-p (design chars)
  (format t "design=~a~%" design)
  (let ((rules (fa-design-rules design))
	(accept-states (fa-design-accept-states design)))
    (accept-state-p
     (nfa-read-chars rules chars (fa-design-start-state design))
     accept-states)))

(defparameter *nfa-rules-1*
	      (make-nfa-rules
	       (make-fa-rule 1 #\a 1) (make-fa-rule 1 #\b 1) (make-fa-rule 1 #\b 2)
	       (make-fa-rule 2 #\a 3) (make-fa-rule 2 #\b 3)
	       (make-fa-rule 3 #\a 4) (make-fa-rule 3 #\b 4)))

(defparameter *nfa-rules-2*
	      (make-nfa-rules
	       (make-fa-rule 1 nil 2) (make-fa-rule 1 nil 4)
	       (make-fa-rule 2 #\a 3)
	       (make-fa-rule 3 #\a 2)
	       (make-fa-rule 4 #\a 5)
	       (make-fa-rule 5 #\a 6)
	       (make-fa-rule 6 #\a 4)))

;; --------------------
;; Regular Expression Abstract Tree
;; --------------------

(defun at-empty ()
  (list :empty))

(defun at-literal (char)
  (list :literal char))

(defun at-literal-char (exp)
  (cadr exp))

(defun at-concatenate (first second)
  (list :concatenate first second))

(defun at-concatenate-first (exp)
  (cadr exp))

(defun at-concatenate-second (exp)
  (caddr exp))

(defun at-choose (first second)
  (list :choose first second))

(defun at-choose-first (exp)
  (cadr exp))

(defun at-choose-second (exp)
  (caddr exp))

(defun at-repeat (pattern)
  (list :repeat pattern))

(defun at-repeat-pattern (exp)
  (cadr exp))

(defun at-exp-type (exp)
  (car exp))

(defparameter *at-precedence-assoc*
	      '((:empty . 3)
		(:literal . 3)
		(:concatenate . 1)
		(:choose . 0)
		(:repeat . 2)))

(defun at-precedence (exp)
  (let ((type (at-exp-type exp)))
    (cdr (assoc type *at-precedence-assoc*))))

(defun at-exp-to-string (exp)
  (flet ((bracket (inner-exp outer-exp)
	   (format nil
		   (if (< (at-precedence inner-exp) (at-precedence outer-exp))
		       "(~a)"
		       "~a")
		   (at-exp-to-string inner-exp))))
   (let ((type (at-exp-type exp)))
     (format t "exp=~a~%" exp)
     (case type
       (:empty "empty")
       (:literal (format nil "~a" (at-literal-char exp)))
       (:concatenate
	(format nil "~a~a"
		(bracket (at-concatenate-first exp) exp)
		(bracket (at-concatenate-second exp) exp)))
       (:choose
	(format nil "~a|~a"
		(bracket (at-choose-first exp) exp)
		(bracket (at-choose-second exp) exp)))
       (:repeat
	(format nil "~a*"
		(bracket (at-repeat-pattern exp) exp)))))))

(defun at-exp-to-nfa-design (exp)
  (let ((state 0))
    (labels ((new-state ()
	       (incf state)
	       state)
	     (to-nfa-design (exp)
	       (let ((type (at-exp-type exp)))
		 (case type
		   (:empty
		    (make-fa-design (make-nfa-rules) '()))
		   (:literal
		    (let ((start-state (new-state))
			  (accept-state (new-state)))
		      (make-fa-design
		       (make-nfa-rules
			(make-fa-rule start-state (at-literal-char exp) accept-state))
		       (list accept-state))))
		   (:concatenate
		    (let* ((first-design
			    (to-nfa-design (at-concatenate-first exp)))
			   (second-design
			    (to-nfa-design (at-concatenate-second exp)))
			   (second-start-state
			    (fa-design-start-state second-design))
			   (second-accept-states
			    (fa-design-accept-states second-design))
			   (first-to-second-rules
			     (mapcar
			      #'(lambda (state)
				  (make-fa-rule state nil second-start-state))
			      (fa-design-accept-states first-design)))
			   (rules (append (fa-design-rules first-design)
					  (fa-design-rules second-design)
					  first-to-second-rules)))
		      (format t "~a~%" rules)
		      (make-fa-design
		       (apply #'make-nfa-rules rules)
		       second-accept-states)))
		   (:choose
		    (let* ((first-design
			    (to-nfa-design (at-choose-first exp)))
			   (second-design
			    (to-nfa-design (at-choose-second exp)))
			   (start-state (new-state))
			   (connect-rules
			    (list (make-fa-rule start-state nil (fa-design-start-state first-design))
				  (make-fa-rule start-state nil (fa-design-start-state second-design))))
			   (rules
			    (append connect-rules
				    (fa-design-rules first-design)
				    (fa-design-rules second-design))))
		      (make-fa-design
		       (apply #'make-nfa-rules rules)
		       (append (fa-design-accept-states first-design)
			       (fa-design-accept-states second-design)))))
		   (:repeat
		    (let* ((design
			    (to-nfa-design (at-repeat-pattern exp)))
			   (start-state (new-state))
			   (rules
			    (append
			     (list
			      (make-fa-rule start-state nil (fa-design-start-state design)))
			     (fa-design-rules design)
			     (mapcar
			      #'(lambda (state)
				  (make-fa-rule state nil (fa-design-start-state design)))
			      (fa-design-accept-states design)))))
		      (make-fa-design
		       (apply #'make-nfa-rules
			      rules)
		       (append (list start-state) (fa-design-accept-states design)))))
		   ))))
      (to-nfa-design exp))))

(defparameter *pattern1*
	      (at-repeat
	       (at-choose
		(at-concatenate (at-literal #\a) (at-literal #\b))
		(at-literal #\a))))

;; (a|b)(a|c)
(defparameter *pattern2*
	      (at-concatenate
	       (at-choose (at-literal #\a) (at-literal #\b))
	       (at-choose (at-literal #\a) (at-literal #\c))))

(defparameter *pattern3*
	      (at-repeat
	       (at-concatenate
		(at-literal #\a)
		(at-choose (at-literal #\a) (at-literal #\b)))))
