-- Prove2me | solution 1 for mme_CW_square_grade_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:50:15.973605+00:00
-- url     : https://prove2.me/submissions/02de2877-dddc-4767-81fe-020ae7bb347d

import Mathlib.Tactic

/-!
# The fifteen five-grade types in the CW tensor square

After regrouping the two canonical CW grades in each mode, all coordinates
lie in `Fin 5` and the support equation is `I + J + K = 4`.  This theorem
enumerates the fifteen possibilities used in equation (11) and separates the
four cyclic-orbit shapes `(0,0,4)`, `(0,1,3)`, `(0,2,2)`, and `(1,1,2)`.
-/

theorem solution
    (I J K : Fin 5)
    (hsum : I.val + J.val + K.val = 4) :
    (I, J, K) = (0, 0, 4) ∨
    (I, J, K) = (0, 1, 3) ∨
    (I, J, K) = (0, 2, 2) ∨
    (I, J, K) = (0, 3, 1) ∨
    (I, J, K) = (0, 4, 0) ∨
    (I, J, K) = (1, 0, 3) ∨
    (I, J, K) = (1, 1, 2) ∨
    (I, J, K) = (1, 2, 1) ∨
    (I, J, K) = (1, 3, 0) ∨
    (I, J, K) = (2, 0, 2) ∨
    (I, J, K) = (2, 1, 1) ∨
    (I, J, K) = (2, 2, 0) ∨
    (I, J, K) = (3, 0, 1) ∨
    (I, J, K) = (3, 1, 0) ∨
    (I, J, K) = (4, 0, 0) := by
  fin_cases I <;> fin_cases J <;> fin_cases K <;> simp_all
