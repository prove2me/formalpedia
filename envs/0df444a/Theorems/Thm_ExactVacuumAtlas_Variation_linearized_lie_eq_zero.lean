-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_linearized_lie_eq_zero
-- name    : ExactVacuumAtlas.Variation.linearized_lie_eq_zero
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:51:59.91375+00:00
-- url     : https://prove2.me/theorems/2abc44a3-c87a-4764-aa37-934c25483201
-- title:
--   Coordinate (diffeomorphism) gauge directions solve the linearised equations
-- statement:
--   Coordinate (diffeomorphism) gauge directions solve the linearised equations
--
--   For an Einstein–Maxwell certificate (g, gi, F) on U and any C^∞ vector field ξ on U (four components), at every x ∈ U: LE(g, gi, F; L_ξ g, L_ξ F) = 0, LJ(…) = 0, LH(L_ξ F) = 0, where (L_ξ T)_ab = Σ_c (ξ^c ∂_c T_ab + T_cb ∂_a ξ^c + T_ac ∂_b ξ^c) (lieCov2).
--
--   **Scope.** Proof uses the local coordinate family Φ_ε(y) = y + εξ(y) on the open domain shiftDom (y ∈ U, Φ_ε y ∈ U, det(1 + εDξ) ≠ 0); Φ_ε is a local family of coordinate maps, not a proved integral flow of ξ and not a global flow. No gauge classification.
--
--   **中文摘要** 任意 C^∞ 的 ξ：Lie 导数方向 (L_ξ g, L_ξ F) 满足线性化方程。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Gauge.lean#L193-L269; SHA-256 46d8b5f079abb433286efd867efe3e39da3c640c54b8be946e36e83eaf1a0127. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Gauge
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}

theorem ExactVacuumAtlas.Variation.linearized_lie_eq_zero {U : Set (Pt 4)} {g gi : Metric 4} {F : TwoForm 4}
    (hcert : EinsteinMaxwellCertificate g gi F U) {ξ : Fin 4 → Pt 4 → ℝ} (hξ : ∀ k, ContDiffOn ℝ ∞ (ξ k) U)
    {x : Pt 4} (hx : x ∈ U) :
    (∀ a b, linEinstein g gi F (lieCov2 ξ g) (lieCov2 ξ F) a b x = 0) ∧
    (∀ b, linMaxwell g gi F (lieCov2 ξ g) (lieCov2 ξ F) b x = 0) ∧
    (∀ a b c, linFaraday (lieCov2 ξ F) a b c x = 0) := by sorry
