-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_polyhedral_lconvex_argmin_is_lconvex_polyhedron
-- name    : DiscreteConvex.LConvexFunctionsC.polyhedral_lconvex_argmin_is_lconvex_polyhedron
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:38:49.857352+00:00
-- url     : https://prove2.me/theorems/30e1b262-4b94-4366-b19e-9f867a2e2951
-- title:
--   Proposition 7.34 -- polyhedral_lconvex_argmin_is_lconvex_polyhedron
-- statement:
--   **Proposition 7.34** (p.193). Let $g\in L[\mathbb R\to\mathbb R]$ be a polyhedral L-convex function. For any $x\in\mathbb R^V$, $\arg\min g[-x]$ is an L-convex polyhedron if it is not empty.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.193, Proposition 7.34.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.193, Proposition 7.34

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LConvexPolyhedronR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ArgMinR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LinearWeightR

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.34 (p.193). The minimizer set of a linearly-perturbed polyhedral L-convex
function is an L-convex polyhedron of the class `L⁰[R]`, if nonempty. The class is the real one,
not the integral hull class `L⁰[Z|R]`: for `g(p) = max(p₁ - p₂ - 1/2, 0)` and `x = 0` the
minimizer set is `{p : p₁ - p₂ ≤ 1/2}`, which is the convex hull of no integer set. -/
theorem polyhedral_lconvex_argmin_is_lconvex_polyhedron (g : (V → ℝ) → WithTop ℝ)
    (hg : SBFR g ∧ TRFR g) (hpoly : IsPolyhedralConvex g) (x : V → ℝ)
    (hne : (ArgMinR (LinearWeightR g (fun v => - x v))).Nonempty) :
    LConvexPolyhedronR (ArgMinR (LinearWeightR g (fun v => - x v))) := by sorry

end DiscreteConvex.LConvexFunctionsC
