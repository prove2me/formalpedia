-- Prove2me | Theorems.Thm_DiscreteConvex_Algorithms_steepest_descent_unique_minimizer_bound
-- name    : DiscreteConvex.Algorithms.steepest_descent_unique_minimizer_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T03:35:56.876364+00:00
-- url     : https://prove2.me/theorems/f07a78ad-fb92-48e9-a5cb-3cae31e43385
-- title:
--   Proposition 10.1 -- iteration bound under a unique minimizer
-- statement:
--   **Proposition 10.1** (p.282). If $f$ has a unique minimizer $x^*$, the number of iterations in the steepest descent algorithm is bounded by $\|x^0 - x^*\|_1 / 2$, where $x^0$ is the initial vector found in step S0 — formalized as $2N \le \|x^0 - x^*\|_1$ for any run of $N$ iterations, avoiding a division that need not land on an integer a priori (the book separately notes $\|x^0-x^*\|_1$ is always even, but this item does not need that fact to state the bound faithfully).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Proposition 10.1.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Proposition 10.1

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_Algorithms_IsSteepestDescentRun
import Definitions.Def_DiscreteConvex_Algorithms_L1Dist

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.Algorithms

/-- Proposition 10.1 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.282). If `f` has a
unique minimizer `x*`, the number of iterations in the steepest descent algorithm is bounded
by `‖x⁰ - x*‖₁ / 2`, where `x⁰` is the initial vector found in step S0. -/
theorem steepest_descent_unique_minimizer_bound {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (xstar : V → ℤ)
    (hxstar : ArgMin f = {xstar}) (x0 : V → ℤ) (hx0 : x0 ∈ DomZ f) (x : ℕ → V → ℤ) (N : ℕ)
    (hrun : IsSteepestDescentRun f x0 x N) :
    2 * N ≤ L1Dist x0 xstar := by sorry

end DiscreteConvex.Algorithms
