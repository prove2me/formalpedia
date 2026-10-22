-- Prove2me | Theorems.Thm_AKS_prime_iff
-- name    : AKS.prime_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T12:54:17.077025+00:00
-- url     : https://prove2.me/theorems/0505534a-95b2-4528-8f3a-24292c742bfe
-- title:
--   The AKS test returns PRIME exactly for the primes (Theorem 4.1)
-- statement:
--   Theorem 4.1 of Agrawal, Kayal, and Saxena's paper (Annals of Mathematics 160 (2004) 781-793), the paper's central theorem and the goal of this mission: the algorithm of Section 4 returns PRIME if and only if n is prime. The forward direction is Lemma 4.2 - a prime is never a perfect power, has no nontrivial gcd witnesses, and satisfies congruence (2) for every a and r by Lemma 2.1, so no step rejects it. The backward direction runs the introspective machinery: if the algorithm accepts in step 4, some gcd witness below the square root would have caught a composite; if it accepts in step 6, then with r the search's choice and p a prime factor of n with ordR r p > 1, the group G of residues of I = {(n/p)^i p^j} has t > log^2 n elements, and the images of P in F_p[X]/(h) form a group of size at least C(t + ell, t - 1) by Lenstra's Lemma 4.7 and at most n^(sqrt t) by the Kalai-Sahai-Sudan Lemma 4.8 unless n is a power of p; the bounds collide, so n = p^k, and step 1 forces k = 1: n is prime.
--
--   **Formalization Note** The statement is over the algorithm layer's literal transcription aksDecide of the six steps, for every natural number n (the algorithm answers COMPOSITE for n at most 1, which are not prime). This is the goal statement of the mission.
-- source:
--   M. Agrawal, N. Kayal, N. Saxena, PRIMES is in P, Ann. of Math. 160 (2004) 781-793, Section 4 (Theorem 4.1).

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg

namespace AKS

/-!  Theorem 4.1 of the paper: the algorithm returns PRIME if and only if n
is prime. This is the goal of the mission.  -/
theorem prime_iff : ∀ n : ℕ, aksDecide n = AksResult.prime ↔ Nat.Prime n := by sorry

end AKS
