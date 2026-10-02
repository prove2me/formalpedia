-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_lnat_convex_is_integrally_convex_and_extensible
-- name    : DiscreteConvex.LConvexFunctionsC.lnat_convex_is_integrally_convex_and_extensible
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:51:46.61674+00:00
-- url     : https://prove2.me/theorems/8e8a3e9e-2948-45bf-a423-d67c0a46aabe
-- title:
--   Theorem 7.20 -- lnat_convex_is_integrally_convex_and_extensible
-- statement:
--   **Theorem 7.20** (p.189). An L$^\natural$-convex function is integrally convex. In particular, an L$^\natural$-convex function is convex extensible.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.189, Theorem 7.20.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.189, Theorem 7.20

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsIntegrallyConvexFunction

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.20 (p.189). An L♮-convex function is integrally convex and convex extensible. -/
theorem lnat_convex_is_integrally_convex_and_extensible (g : (V → ℤ) → WithTop ℝ)
    (hg : LNaturalConvex g) :
    IsIntegrallyConvexFunction g ∧ ConvexExtensible g := by sorry

end DiscreteConvex.LConvexFunctionsC
