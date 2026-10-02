-- Prove2me | Theorems.Thm_DiscreteConvex_Algorithms_steepest_descent_K1_bound
-- name    : DiscreteConvex.Algorithms.steepest_descent_K1_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T03:41:03.45127+00:00
-- url     : https://prove2.me/theorems/a1e63588-2bcf-4bfb-97d1-7921af7c823e
-- title:
--   Proposition 10.2 -- iteration bound with tie-breaking (goal)
-- statement:
--   **Proposition 10.2** (p.282). For an M-convex function $f$ with finite $K_1$ (Eq. (10.1)), the number of iterations in the steepest descent algorithm **with the tie-breaking rule (10.2)** is bounded by $K_1/2$ — formalized as $2N \le K_1$ for any run of $N$ iterations using the tie-breaking rule, matching Proposition 10.1's division-avoiding style. Unlike Proposition 10.1, this bound holds for an $f$ with possibly many minimizers, and genuinely needs the specific lexicographic tie-breaking rule (10.2), not an arbitrary choice among tied steepest pairs.
--
--   **Formalization scope.** The book's own "hence... the algorithm finds a minimizer of $f$ in $O(F \cdot n^2 K_1)$ time" corollary is not separately drafted: it combines this iteration bound with the (separately stated, non-numbered) fact that each iteration costs $O(n^2)$ function evaluations, and formalizing "time" and "$F$" (an upper bound on the cost of one evaluation of $f$) would need a cost-model primitive this mission does not otherwise use; the iteration bound itself is this proposition's substantive combinatorial content and is drafted at full strength.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Proposition 10.2.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Proposition 10.2

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_Algorithms_IsSteepestDescentRunTieBreak
import Definitions.Def_DiscreteConvex_Algorithms_IsK1

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.Algorithms

/-- Proposition 10.2 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.282). For an M-convex
function `f` with finite `K1` (Eq. (10.1)), the number of iterations in the steepest descent
algorithm with tie-breaking rule (10.2) is bounded by `K1 / 2`. -/
theorem steepest_descent_K1_bound {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (φ : V → ℕ) (hphi : Function.Injective φ)
    (k1 : ℕ) (hK1 : IsK1 f k1) (x0 : V → ℤ) (hx0 : x0 ∈ DomZ f) (x : ℕ → V → ℤ) (N : ℕ)
    (hrun : IsSteepestDescentRunTieBreak f φ x0 x N) :
    2 * N ≤ k1 := by sorry

end DiscreteConvex.Algorithms
