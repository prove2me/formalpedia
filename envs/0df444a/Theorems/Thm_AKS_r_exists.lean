-- Prove2me | Theorems.Thm_AKS_r_exists
-- name    : AKS.r_exists
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T12:51:44.191027+00:00
-- url     : https://prove2.me/theorems/3ef74001-6eb5-4784-a118-19679f5ce178
-- title:
--   A small r with o_r(n) > log^2 n (Lemma 4.3)
-- statement:
--   Lemma 4.3 of the paper: for n > 1 there exists an r, bounded by the fifth power of the logarithm of n, such that the multiplicative order of n modulo r exceeds the square of the logarithm of n. The proof is a counting argument: every r whose order of n is at most log^2 n, and every r dividing n, divides the single product of n with the numbers n^i - 1 for i up to log^2 n, a product below the power 2^(log^5 n); the lcm of the first log^5 n numbers is at least 2^(log^5 n) by Lemma 3.1, so some r in the window escapes the bad list.
--
--   **Formalization Note** The statement uses the generous integer encoding logUp n = floor(log2 n) + 1, strictly greater than log2 n, in place of the paper's real-valued logarithm, both in the threshold and in the bound: r exists with 1 < r at most max 3 (logUp n)^5 and ordR r n greater than (logUp n)^2. The generosity is one-sided in the safe direction: the algorithm's search for r happens inside exactly this window, and the larger threshold only strengthens the group bound that the correctness proof needs.
-- source:
--   M. Agrawal, N. Kayal, N. Saxena, PRIMES is in P, Ann. of Math. 160 (2004) 781-793, Section 4 (Lemma 4.3).

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg

namespace AKS

/-!  Lemma 4.3 of the paper: a small r with o_r(n) > log^2 n.  -/
theorem r_exists (n : ℕ) (hn : 1 < n) :
    ∃ r, 1 < r ∧ r ≤ max 3 ((logUp n) ^ 5) ∧ (logUp n) ^ 2 < ordR r n := by sorry

end AKS
