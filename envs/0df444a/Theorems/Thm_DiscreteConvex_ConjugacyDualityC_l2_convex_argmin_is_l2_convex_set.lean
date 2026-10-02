-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_l2_convex_argmin_is_l2_convex_set
-- name    : DiscreteConvex.ConjugacyDualityC.l2_convex_argmin_is_l2_convex_set
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:45:15.669596+00:00
-- url     : https://prove2.me/theorems/8662c318-857c-476b-8923-2cdbdc91416d
-- title:
--   Proposition 8.40 -- l2_convex_argmin_is_l2_convex_set
-- statement:
--   **Proposition 8.40** (p.230). (1) For an L2-convex function $g$, $\arg\min g$ is L2-convex if nonempty. (2) The L$^\natural_2$ analogue.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.230, Proposition 8.40.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.230, Proposition 8.40

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ArgMin
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2ConvexSet

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.40 (p.230). The minimizer set of an L2-(resp. L♮₂-)convex function is
L2-(resp. L♮₂-)convex, if nonempty. -/
theorem l2_convex_argmin_is_l2_convex_set :
    (∀ g : (V → ℤ) → WithTop ℝ, L2Convex g → (ArgMin g).Nonempty → L2ConvexSet (ArgMin g)) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, LNat2Convex g → (ArgMin g).Nonempty → LNat2ConvexSet (ArgMin g)) := by sorry

end DiscreteConvex.ConjugacyDualityC
