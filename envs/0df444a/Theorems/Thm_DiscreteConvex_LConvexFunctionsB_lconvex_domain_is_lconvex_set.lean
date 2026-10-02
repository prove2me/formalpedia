-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_lconvex_domain_is_lconvex_set
-- name    : DiscreteConvex.LConvexFunctionsB.lconvex_domain_is_lconvex_set
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:25:01.112295+00:00
-- url     : https://prove2.me/theorems/a133d568-a7fa-4b7b-a2b0-5d8c63d47501
-- title:
--   Proposition 7.8 -- lconvex_domain_is_lconvex_set
-- statement:
--   **Proposition 7.8** (p.181). (1) The effective domain of an L-convex function is an L-convex set. (2) The effective domain of an L$^\natural$-convex function is an L$^\natural$-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.181, Proposition 7.8.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.181, Proposition 7.8

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNatConvexSet

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.8 (p.181). The effective domain of an L-convex (resp. L♮-convex) function is
an L-convex (resp. L♮-convex) set. -/
theorem lconvex_domain_is_lconvex_set (g : (V → ℤ) → WithTop ℝ) :
    ((SBF g ∧ TRF g) → (DomZ g).Nonempty → LConvexSet (DomZ g)) ∧
    (LNaturalConvex g → (DomZ g).Nonempty → LNatConvexSet (DomZ g)) := by sorry

end DiscreteConvex.LConvexFunctionsB
