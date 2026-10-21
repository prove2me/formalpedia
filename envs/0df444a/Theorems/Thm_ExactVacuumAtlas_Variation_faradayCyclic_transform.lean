-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_faradayCyclic_transform
-- name    : ExactVacuumAtlas.Variation.faradayCyclic_transform
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:27.213322+00:00
-- url     : https://prove2.me/theorems/8e878407-dc13-459b-b68e-f136b879599d
-- title:
--   Covariance of the H residual
-- statement:
--   Covariance of the H residual
--
--   Under CoordChange U V Φ J K with pulled-back data as in the transport card, the H residual transforms as a covariant 3-tensor; exact index form in the statement.
--
--   **Scope.** Nonlinear (not linearised) transformation law; used by the certificate transport and the gauge argument.
--
--   **中文摘要** H 残差的坐标协变律。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Covariance.lean#L307-L361; SHA-256 9354896334506569e5c4491ef3a59340742907640cf5d1c465ba5a6e2e9ad40b. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.faradayCyclic_transform (hc : CoordChange U V Φ J K) (hFs : ∀ i j, ContDiffOn ℝ ∞ (FV i j) V)
    (hFa : ∀ x ∈ V, ∀ i j, FV i j x = -FV j i x)
    (hF : ∀ y ∈ U, metricMatrix F y = (J y)ᵀ * metricMatrix FV (Φ y) * J y) {y : Pt n} (hy : y ∈ U)
    (a b c : Fin n) :
    faradayCyclic F a b c y =
      ∑ e, ∑ p, ∑ q, J y e a * J y p b * J y q c * faradayCyclic FV e p q (Φ y) := by sorry
