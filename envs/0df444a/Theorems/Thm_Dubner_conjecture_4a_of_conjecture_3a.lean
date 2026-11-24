-- Prove2me | Theorems.Thm_Dubner_conjecture_4a_of_conjecture_3a
-- name    : Dubner.conjecture_4a_of_conjecture_3a
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-24T11:17:24.833149+00:00
-- url     : https://prove2.me/theorems/19dbd64e-e033-48b8-a9e7-fc130ffacdf0
-- title:
--   Dubner: Conjecture 3a implies Conjecture 4a
-- statement:
--   Dubner's Conjecture 3a implies his Conjecture 4a: if every multiple of $6$ greater than $4206$ is a sum of two middle numbers, then every even integer greater than $4208$ is a sum of two t-primes.
--
--   This is the reduction Dubner uses to pass between the two forms of his conjecture.
-- source:
--   H. Dubner, Twin Prime Conjectures, J. Recreational Math. 30(3) (1999-2000); scan https://oeis.org/A007534/a007534.pdf, pp. 1-2, Section 2 (the identities for N, N + 2 and N - 2, and "Conjecture 3a (with a little extra data) implies all the others")

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

namespace Dubner
theorem conjecture_4a_of_conjecture_3a
    (h3a : ∀ N : ℕ, 6 ∣ N → 4206 < N →
      ∃ m₁ m₂ : ℕ, IsMiddleNumber m₁ ∧ IsMiddleNumber m₂ ∧ N = m₁ + m₂) :
    ∀ n : ℕ, 4208 < n → Even n → ∃ p q : ℕ, IsTPrime p ∧ IsTPrime q ∧ n = p + q := by
  sorry
end Dubner
