-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_l2_convex_domain_is_l2_convex_set
-- name    : DiscreteConvex.ConjugacyDualityC.l2_convex_domain_is_l2_convex_set
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:45:30.777242+00:00
-- url     : https://prove2.me/theorems/c4a364c1-4231-46a5-8bc1-20f6750ba856
-- title:
--   Proposition 8.39 -- l2_convex_domain_is_l2_convex_set
-- statement:
--   **Proposition 8.39** (p.230). (1) For an L2-convex function $g$, $\operatorname{dom} g$ is L2-convex. (2) The L$^\natural_2$ analogue.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.230, Proposition 8.39.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.230, Proposition 8.39

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2ConvexSet

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.39 (p.230). The effective domain of an L2-(resp. L♮₂-)convex function is
L2-(resp. L♮₂-)convex. -/
theorem l2_convex_domain_is_l2_convex_set :
    (∀ g : (V → ℤ) → WithTop ℝ, L2Convex g → L2ConvexSet (DomZ g)) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, LNat2Convex g → LNat2ConvexSet (DomZ g)) := by sorry

end DiscreteConvex.ConjugacyDualityC
