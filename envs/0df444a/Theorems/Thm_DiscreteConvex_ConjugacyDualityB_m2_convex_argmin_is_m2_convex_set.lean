-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_m2_convex_argmin_is_m2_convex_set
-- name    : DiscreteConvex.ConjugacyDualityB.m2_convex_argmin_is_m2_convex_set
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:36:31.43722+00:00
-- url     : https://prove2.me/theorems/97aecc97-4b2e-4a09-93f6-1cf2bbb4093c
-- title:
--   Proposition 8.30 -- m2_convex_argmin_is_m2_convex_set
-- statement:
--   **Proposition 8.30** (p.227). (1) For an M2-convex function $f$, $\arg\min f$ is M2-convex if nonempty. (2) The M$^\natural_2$ analogue.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.227, Proposition 8.30.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.227, Proposition 8.30

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ArgMin
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2ConvexSet

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.30 (p.227). The minimizer set of an M2-(resp. M♮₂-)convex function is
M2-(resp. M♮₂-)convex, if nonempty. -/
theorem m2_convex_argmin_is_m2_convex_set :
    (∀ f : (V → ℤ) → WithTop ℝ, M2Convex f → (ArgMin f).Nonempty → M2ConvexSet (ArgMin f)) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNat2Convex f → (ArgMin f).Nonempty → MNat2ConvexSet (ArgMin f)) := by sorry

end DiscreteConvex.ConjugacyDualityB
