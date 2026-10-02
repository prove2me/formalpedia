-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_lconvex_is_lnat_convex_iff_trf
-- name    : DiscreteConvex.LConvexFunctionsB.lconvex_is_lnat_convex_iff_trf
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:24:12.787735+00:00
-- url     : https://prove2.me/theorems/3916b59d-0607-4725-bf18-f11553fc50b8
-- title:
--   Theorem 7.3 -- lconvex_is_lnat_convex_iff_trf
-- statement:
--   **Theorem 7.3** (p.179). An L-convex function is L$^\natural$-convex. Conversely, an L$^\natural$-convex function is L-convex if and only if it satisfies (TRF[Z]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.179, Theorem 7.3.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.179, Theorem 7.3

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.3 (p.179). An L-convex function is L♮-convex; conversely an L♮-convex function is
L-convex iff it satisfies (TRF[Z]). -/
theorem lconvex_is_lnat_convex_iff_trf (g : (V → ℤ) → WithTop ℝ) :
    ((SBF g ∧ TRF g) → LNaturalConvex g) ∧
    (LNaturalConvex g → (TRF g → SBF g)) := by sorry

end DiscreteConvex.LConvexFunctionsB
