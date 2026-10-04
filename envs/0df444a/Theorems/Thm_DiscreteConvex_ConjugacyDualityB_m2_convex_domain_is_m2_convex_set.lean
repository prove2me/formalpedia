-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_m2_convex_domain_is_m2_convex_set
-- name    : DiscreteConvex.ConjugacyDualityB.m2_convex_domain_is_m2_convex_set
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T01:36:20.287182+00:00
-- url     : https://prove2.me/theorems/dadbaa0a-9868-4164-ab11-ac7a980f795e
-- title:
--   Proposition 8.29 -- m2_convex_domain_is_m2_convex_set
-- statement:
--   **Proposition 8.29** (p.227). (1) For an M2-convex function $f$, $\operatorname{dom} f$ is M2-convex. (2) For an M$^\natural_2$-convex function $f$, $\operatorname{dom} f$ is M$^\natural_2$-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.227, Proposition 8.29.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.227, Proposition 8.29

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2ConvexSet

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.29 (p.227). The effective domain of an M2-(resp. M♮₂-)convex function is
M2-(resp. M♮₂-)convex. -/
theorem m2_convex_domain_is_m2_convex_set :
    (∀ f : (V → ℤ) → WithTop ℝ, M2Convex f → M2ConvexSet (DomZ f)) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNat2Convex f → MNat2ConvexSet (DomZ f)) := by sorry

end DiscreteConvex.ConjugacyDualityB
