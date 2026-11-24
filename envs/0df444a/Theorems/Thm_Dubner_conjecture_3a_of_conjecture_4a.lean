-- Prove2me | Theorems.Thm_Dubner_conjecture_3a_of_conjecture_4a
-- name    : Dubner.conjecture_3a_of_conjecture_4a
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-24T12:44:23.526213+00:00
-- url     : https://prove2.me/theorems/5e4afe94-2f75-47bb-8af8-605481fc9bc7
-- title:
--   Dubner: Conjecture 4a implies Conjecture 3a
-- statement:
--   The converse of Dubner's reduction: if every even integer greater than $4208$ is a sum of two t-primes (Conjecture 4a), then every multiple of $6$ greater than $4206$ is a sum of two middle numbers (Conjecture 3a). Together with the implication from Conjecture 3a to Conjecture 4a, this makes the two conjectures equivalent.
--
--   Dubner states the converse for his Conjectures 3 and 4, which concern sufficiently large numbers. The statement here is the same converse for the sharpened Conjectures 3a and 4a, with their explicit bounds.
-- source:
--   H. Dubner, Twin Prime Conjectures, J. Recreational Math. 30(3) (1999-2000); scan https://oeis.org/A007534/a007534.pdf, p. 2, Section 2 ("Conjecture 3 implies Conjecture 4, Conjecture 1 implies Conjecture 2 and conversely"); the converse for Conjectures 3a and 4a is not written out in the paper

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

namespace Dubner
theorem conjecture_3a_of_conjecture_4a
    (h4a : ∀ n : ℕ, 4208 < n → Even n → ∃ p q : ℕ, IsTPrime p ∧ IsTPrime q ∧ n = p + q) :
    ∀ N : ℕ, 6 ∣ N → 4206 < N →
      ∃ m₁ m₂ : ℕ, IsMiddleNumber m₁ ∧ IsMiddleNumber m₂ ∧ N = m₁ + m₂ := by
  sorry
end Dubner
