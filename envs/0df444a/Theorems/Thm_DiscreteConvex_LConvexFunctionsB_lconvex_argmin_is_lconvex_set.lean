-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_lconvex_argmin_is_lconvex_set
-- name    : DiscreteConvex.LConvexFunctionsB.lconvex_argmin_is_lconvex_set
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:22:33.787048+00:00
-- url     : https://prove2.me/theorems/341e4cc4-3d08-489f-8a76-6eb203d64c39
-- title:
--   Proposition 7.16 -- lconvex_argmin_is_lconvex_set
-- statement:
--   **Proposition 7.16** (p.186). For an L-convex function $g\in L[\mathbb Z\to\mathbb R]$, $\arg\min g$ is an L-convex set if it is not empty.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, Proposition 7.16.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186, Proposition 7.16

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ArgMin
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LConvexSet

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.16 (p.186). The minimizer set of an L-convex function is an L-convex set, if
nonempty. -/
theorem lconvex_argmin_is_lconvex_set (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g)
    (hne : (ArgMin g).Nonempty) : LConvexSet (ArgMin g) := by sorry

end DiscreteConvex.LConvexFunctionsB
