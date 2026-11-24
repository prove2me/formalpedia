-- Prove2me | solution 3 for twin_prime_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-24T13:03:43.442332+00:00
-- url     : https://prove2.me/submissions/5aba89e2-9fcd-4167-a9f3-bd4e4bcda716
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Dubner_conjecture_4a
import Theorems.Thm_Dubner_twin_primes_infinite_of_conjecture_4a

/-- The twin prime conjecture, reduced to Dubner's Conjecture 4a:
`Dubner.twin_primes_infinite_of_conjecture_4a` turns `Dubner.conjecture_4a` into the statement of
`twin_prime_conjecture`. -/
theorem solution :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite :=
  Dubner.twin_primes_infinite_of_conjecture_4a Dubner.conjecture_4a
