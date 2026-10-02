-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_mnat2_convex_is_integrally_convex
-- name    : DiscreteConvex.ConjugacyDualityB.mnat2_convex_is_integrally_convex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:36:49.009988+00:00
-- url     : https://prove2.me/theorems/6c193470-8394-4711-bfe4-47caed5d5af1
-- title:
--   Theorem 8.31 -- mnat2_convex_is_integrally_convex
-- statement:
--   **Theorem 8.31** (p.227). An M$^\natural_2$-convex function is integrally convex; in particular, an M$^\natural_2$-convex set is integrally convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.227, Theorem 8.31.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.227, Theorem 8.31

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegrallyConvexFunction
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegrallyConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2ConvexSet

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.31 (p.227). An M♮₂-convex function is integrally convex; in particular, an
M♮₂-convex set is integrally convex. -/
theorem mnat2_convex_is_integrally_convex :
    (∀ f : (V → ℤ) → WithTop ℝ, MNat2Convex f → IsIntegrallyConvexFunction f) ∧
    (∀ D : Set (V → ℤ), MNat2ConvexSet D → IsIntegrallyConvex D) := by sorry

end DiscreteConvex.ConjugacyDualityB
