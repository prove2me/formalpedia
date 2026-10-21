-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_pd_pullback2
-- name    : ExactVacuumAtlas.Variation.pd_pullback2
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:52:58.713965+00:00
-- url     : https://prove2.me/theorems/ce44c91b-cdec-4425-85f8-89b765c144dc
-- title:
--   Partial derivative of a pulled-back 2-form
-- statement:
--   Partial derivative of a pulled-back 2-form
--
--   Under the stated CoordChange, smoothness and pullback hypotheses, the coordinate derivative of F = Jᵀ FV(Φ) J has three product-rule contributions: (∂J)ᵀ FV(Φ) J, Jᵀ ∂(FV∘Φ) J, and Jᵀ FV(Φ) (∂J). The middle term uses the chain rule with ∂FV at Φ(y); the other two contain derivatives of the Jacobian. The formal statement gives the complete indexed sum. This is an intermediate derivative formula, not yet the cancellation in the H transformation law.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 拉回二形式的偏导公式。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Covariance.lean#L281-L305; SHA-256 9354896334506569e5c4491ef3a59340742907640cf5d1c465ba5a6e2e9ad40b. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {FV F : TwoForm n}

theorem ExactVacuumAtlas.Variation.pd_pullback2 (hc : CoordChange U V Φ J K) (hFs : ∀ i j, ContDiffOn ℝ ∞ (FV i j) V)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) {y : Pt n} (hy : y ∈ U)
    (a b c : Fin n) :
    pd a (F b c) y = ∑ p, ∑ q, (pdM a J y p b * FV p q (Φ y) * J y q c +
      J y p b * (∑ e, pd e (FV p q) (Φ y) * J y e a) * J y q c + J y p b * FV p q (Φ y) * pdM a J y q c) := by sorry
