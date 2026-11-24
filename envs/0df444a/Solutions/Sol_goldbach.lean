-- Prove2me | solution 1 for goldbach
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-24T13:03:41.777466+00:00
-- url     : https://prove2.me/submissions/da629793-ccd2-4e27-a018-7f5f30d0bfe1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Dubner_conjecture_4a
import Theorems.Thm_Dubner_goldbach_of_conjecture_4a

/-- Goldbach's conjecture, reduced to Dubner's Conjecture 4a:
`Dubner.goldbach_of_conjecture_4a` turns `Dubner.conjecture_4a` into the statement of `goldbach`. -/
theorem solution :
    ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q :=
  Dubner.goldbach_of_conjecture_4a Dubner.conjecture_4a
