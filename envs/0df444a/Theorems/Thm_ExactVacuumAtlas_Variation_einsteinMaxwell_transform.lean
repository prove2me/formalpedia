-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_einsteinMaxwell_transform
-- name    : ExactVacuumAtlas.Variation.einsteinMaxwell_transform
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:24.616833+00:00
-- url     : https://prove2.me/theorems/b9fad51c-983f-49f3-8f34-2fb93e5fb729
-- title:
--   Covariance of the E residual
-- statement:
--   Covariance of the E residual
--
--   Under CoordChange U V Φ J K with pulled-back data as in the transport card, the E residual transforms as a covariant 2-tensor (Jᵀ · E · J); exact index form in the statement.
--
--   **Scope.** Nonlinear (not linearised) transformation law; used by the certificate transport and the gauge argument.
--
--   **中文摘要** E 残差的坐标协变律。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Covariance.lean#L261-L270; SHA-256 9354896334506569e5c4491ef3a59340742907640cf5d1c465ba5a6e2e9ad40b. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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
variable {U V : Set (Pt 4)} {Φ : Pt 4 → Pt 4} {J K : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ}
  {gV giV : Metric 4} {FV : TwoForm 4} {g gi : Metric 4} {F : TwoForm 4}

theorem ExactVacuumAtlas.Variation.einsteinMaxwell_transform (hc : CoordChange U V Φ J K) (hm : MetricData gV giV V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix gV (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix giV (Φ y) * (K y)ᵀ)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) {y : Pt 4} (hy : y ∈ U) :
    Matrix.of (fun a b => einsteinMaxwell g gi F a b y) =
      (J y)ᵀ * Matrix.of (fun a b => einsteinMaxwell gV giV FV a b (Φ y)) * J y := by sorry
