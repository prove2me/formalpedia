-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_maxwellDiv_transform
-- name    : ExactVacuumAtlas.Variation.maxwellDiv_transform
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:56.956491+00:00
-- url     : https://prove2.me/theorems/7259acf7-7146-435c-9786-7dfe8d5605e8
-- title:
--   Covariance of the J residual
-- statement:
--   Covariance of the J residual
--
--   Under CoordChange U V Φ J K with pulled-back data as in the transport card, the J residual transforms as a contravariant vector (acted on by the inverse Jacobian K); exact index form in the statement.
--
--   **Scope.** Nonlinear (not linearised) transformation law; used by the certificate transport and the gauge argument.
--
--   **中文摘要** J 残差的坐标协变律。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Covariance.lean#L184-L221; SHA-256 9354896334506569e5c4491ef3a59340742907640cf5d1c465ba5a6e2e9ad40b. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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
  {gV giV : Metric n} {FV : TwoForm n} {g gi : Metric n} {F : TwoForm n}

theorem ExactVacuumAtlas.Variation.maxwellDiv_transform (hc : CoordChange U V Φ J K) (hm : MetricData gV giV V)
    (hFs : ∀ i j, ContDiffOn ℝ ∞ (FV i j) V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix gV (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix giV (Φ y) * (K y)ᵀ)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) {y : Pt n} (hy : y ∈ U)
    (b : Fin n) :
    maxwellDiv g gi F b y = ∑ q, K y b q * maxwellDiv gV giV FV q (Φ y) := by sorry
