-- Prove2me | Theorems.Thm_AKS_poly_time
-- name    : AKS.poly_time
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T12:53:56.815598+00:00
-- url     : https://prove2.me/theorems/b57b497a-74b8-4291-9eba-96df4e3c0c2e
-- title:
--   The polynomial work bound for the algorithm (Section 5)
-- statement:
--   The time analysis of Section 5 of the paper, in generous integer form. The work measure aksWork charges the algorithm's arithmetic at schoolbook granularity: logUp(n)^6 for the perfect-power test of step 1, r(logUp n + 1) for the r-search of step 2 and the gcd loop of step 3, and (ell r n)(logUp n + 1)(r + 1)^2 for the congruence loop of step 5 - each congruence being logUp n + 1 multiplications of degree-r polynomials with log n-sized coefficients. Since the r-search stays inside the window of Lemma 4.3 (r at most max 3 (logUp n)^5), ell r n is at most the square root of r times logUp n, and the total is bounded by a constant times the fifteenth power of logUp n - a generous integer form of the paper's Theorem 5.1 bound of O~(log^(21/2) n), which carries the unconditional membership of PRIMES in P.
--
--   **Formalization Note** The bound is stated on the explicit computable measure aksWork, so the polynomial-time claim is anchored in the formal fragment itself; the correspondence between arithmetic-work measures and Turing-machine bit complexity (the O~(m) arithmetic of the paper's Section 5) is carried in prose.
-- source:
--   M. Agrawal, N. Kayal, N. Saxena, PRIMES is in P, Ann. of Math. 160 (2004) 781-793, Section 5 (Theorem 5.1).

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg

namespace AKS

/-!  The work bound of Section 5 of the paper, in generous integer form:
the work measure of the algorithm is bounded by a constant times the
fifteenth power of logUp n.  -/
theorem poly_time : ∃ C : ℕ, ∀ n : ℕ, aksWork n ≤ C * (logUp n) ^ 15 := by sorry

end AKS
