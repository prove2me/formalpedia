-- Prove2me | Theorems.Thm_Dubner_conjecture_4a
-- name    : Dubner.conjecture_4a
-- status  : Open
-- author  : @Idealson
-- created : 2026-11-24T11:03:30.692646+00:00
-- url     : https://prove2.me/theorems/6879b238-9f19-4d7c-ad74-eb39a0e71bc9
-- title:
--   Dubner's conjecture: every even $n>4208$ is a sum of two twin-prime members
-- statement:
--   **Dubner's Conjecture 4a.** Every even integer greater than $4208$ is the sum of two t-primes, that is, of two primes each of which has a twin:
--
--   $$\forall n>4208,\ n \text{ even} \implies \exists\, p,q \text{ t-primes with } n=p+q.$$
--
--   The two summands need not belong to the same twin pair. The bound $4208$ is sharp: $4204$, $4206$ and $4208$ are not such sums. The conjecture implies both Goldbach's conjecture and the twin prime conjecture.
-- source:
--   H. Dubner, Twin Prime Conjectures, J. Recreational Math. 30(3) (1999-2000); scan https://oeis.org/A007534/a007534.pdf, p. 2, Section 2, Conjecture 4a

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

namespace Dubner
theorem conjecture_4a :
    ∀ n : ℕ, 4208 < n → Even n → ∃ p q : ℕ, IsTPrime p ∧ IsTPrime q ∧ n = p + q := by
  sorry
end Dubner
