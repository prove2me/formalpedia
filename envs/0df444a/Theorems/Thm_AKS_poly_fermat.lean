-- Prove2me | Theorems.Thm_AKS_poly_fermat
-- name    : AKS.poly_fermat
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T12:50:41.61156+00:00
-- url     : https://prove2.me/theorems/5ac26fbc-e207-4aeb-996c-16f22d30e408
-- title:
--   The polynomial Fermat characterization of the primes (Lemma 2.1)
-- statement:
--   Lemma 2.1 of Agrawal, Kayal, and Saxena's paper (Annals of Mathematics 160 (2004) 781-793): the generalization of Fermat's Little Theorem to polynomial rings. For n at least 2 and a coprime to n, n is prime if and only if (X + a)^n = X^n + a in the polynomial ring over Z_n. The forward direction is the freshman's dream in Z_p[X] - every binomial coefficient C(p, i) with 0 < i < p is divisible by p - together with Fermat's little theorem for the base a. The backward direction isolates the coefficient of X^q, for a prime q with q^k dividing n exactly: the coefficient is C(n, q) a^(n-q), whose q-adic valuation falls below k because q^k does not divide C(n, q) and q does not divide a, so the identity fails in Z_n[X].
--
--   **Formalization Note** The congruence is stated as the definition polyFermat n a, an equality in Polynomial (ZMod n); the coprimality of a and n is a hypothesis, as in the paper.
-- source:
--   M. Agrawal, N. Kayal, N. Saxena, PRIMES is in P, Ann. of Math. 160 (2004) 781-793, Section 2 (Lemma 2.1).

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg

namespace AKS

/-!  Lemma 2.1 of the paper: the polynomial Fermat characterization of the
primes.  -/
theorem poly_fermat (n a : ℕ) (hn : 2 ≤ n) (ha : Nat.gcd a n = 1) :
    Nat.Prime n ↔ polyFermat n a := by sorry

end AKS
