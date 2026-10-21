-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_EinsteinMaxwellCertificate_transport
-- name    : ExactVacuumAtlas.Variation.EinsteinMaxwellCertificate.transport
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:55.97415+00:00
-- url     : https://prove2.me/theorems/cd5ed289-bc2b-435e-8198-e4232cee86dc
-- title:
--   Transport of the full Einstein–Maxwell certificate along a coordinate change
-- statement:
--   Transport of the full Einstein–Maxwell certificate along a coordinate change
--
--   Given CoordChange U V Φ J K (Atlas II: U, V open, Φ C^∞ on U with Φ(U) ⊆ V, J the genuine Jacobian of Φ, J · K = 1 on U), U nonempty, a certificate for (gV, giV, FV) on V, and data on U with g = Jᵀ gV(Φ) J, gi = K giV(Φ) Kᵀ, F = Jᵀ FV(Φ) J on U: then EinsteinMaxwellCertificate g gi F U.
--
--   **Scope.** Every field of the certificate is transported, using the proved covariance of E (2-tensor), J (vector, with K) and H (3-tensor); it is not the Atlas II Ricci law relabelled.
--
--   **中文摘要** 完整 EM 证书沿坐标变换（CoordChange）传递：拉回度规、逆与场后，所有字段（含 E、J、H=0）在 U 上成立。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Covariance.lean#L367-L423; SHA-256 9354896334506569e5c4491ef3a59340742907640cf5d1c465ba5a6e2e9ad40b. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.EinsteinMaxwellCertificate.transport {U V : Set (Pt 4)} {Φ : Pt 4 → Pt 4}
    {J K : Pt 4 → Matrix (Fin 4) (Fin 4) ℝ} {gV giV : Metric 4} {FV : TwoForm 4} {g gi : Metric 4}
    {F : TwoForm 4} (hc : CoordChange U V Φ J K) (hne : U.Nonempty)
    (hcert : EinsteinMaxwellCertificate gV giV FV V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix gV (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix giV (Φ y) * (K y)ᵀ)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) :
    EinsteinMaxwellCertificate g gi F U := by sorry
