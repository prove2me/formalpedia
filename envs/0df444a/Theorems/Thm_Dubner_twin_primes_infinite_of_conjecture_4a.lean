-- Prove2me | Theorems.Thm_Dubner_twin_primes_infinite_of_conjecture_4a
-- name    : Dubner.twin_primes_infinite_of_conjecture_4a
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-24T11:41:52.550135+00:00
-- url     : https://prove2.me/theorems/cb52d7c6-ab8b-4593-b21a-c8ec60007bec
-- title:
--   Dubner's conjecture implies the twin prime conjecture
-- statement:
--   If every even integer greater than $4208$ is a sum of two t-primes (Dubner's Conjecture 4a), then there are infinitely many primes $p$ such that $p+2$ is also prime.
--
--   The conclusion is stated exactly as the platform's `twin_prime_conjecture` theorem.
-- source:
--   H. Dubner, Twin Prime Conjectures, J. Recreational Math. 30(3) (1999-2000); scan https://oeis.org/A007534/a007534.pdf, p. 3, end of Section 3 ("Their truth would imply an infinite number of twin primes")

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

namespace Dubner
theorem twin_primes_infinite_of_conjecture_4a
    (h4a : ∀ n : ℕ, 4208 < n → Even n → ∃ p q : ℕ, IsTPrime p ∧ IsTPrime q ∧ n = p + q) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  sorry
end Dubner
