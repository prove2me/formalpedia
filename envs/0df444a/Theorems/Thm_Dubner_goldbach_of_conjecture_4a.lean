-- Prove2me | Theorems.Thm_Dubner_goldbach_of_conjecture_4a
-- name    : Dubner.goldbach_of_conjecture_4a
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-24T11:35:53.671322+00:00
-- url     : https://prove2.me/theorems/41083704-caac-4db5-a178-a81e4679d502
-- title:
--   Dubner's conjecture implies Goldbach's conjecture
-- statement:
--   If every even integer greater than $4208$ is a sum of two t-primes (Dubner's Conjecture 4a), then every even integer greater than $2$ is a sum of two primes (Goldbach's conjecture).
--
--   The conclusion is stated exactly as the platform's `goldbach` theorem, so that a proof of Dubner's conjecture yields a reduction of the Goldbach mission.
-- source:
--   H. Dubner, Twin Prime Conjectures, J. Recreational Math. 30(3) (1999-2000); scan https://oeis.org/A007534/a007534.pdf, p. 3, end of Section 3 ("Their truth would imply ... the truth of the Goldbach conjecture")

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

namespace Dubner
theorem goldbach_of_conjecture_4a
    (h4a : ∀ n : ℕ, 4208 < n → Even n → ∃ p q : ℕ, IsTPrime p ∧ IsTPrime q ∧ n = p + q) :
    ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  sorry
end Dubner
