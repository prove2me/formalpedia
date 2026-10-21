-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_coordChange_shift
-- name    : ExactVacuumAtlas.Variation.coordChange_shift
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:49.749128+00:00
-- url     : https://prove2.me/theorems/b73514ea-4117-46e0-a9bd-190cb592f538
-- title:
--   y ↦ y + εξ(y) is a coordinate change
-- statement:
--   y ↦ y + εξ(y) is a coordinate change
--
--   For each ε: CoordChange {y : (ε, y) ∈ shiftDom U ξ} U (shiftMap ξ ε) (shiftJac ξ ε) (shiftJac ξ ε)⁻¹ (local; not an integral flow).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 每个 ε 的 y+εξ(y) 构成局部坐标变换。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Gauge.lean#L124-L138; SHA-256 46d8b5f079abb433286efd867efe3e39da3c640c54b8be946e36e83eaf1a0127. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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
variable {U : Set (Pt n)} (hU : IsOpen U) {ξ : Fin n → Pt n → ℝ} (hξ : ∀ k, ContDiffOn ℝ ∞ (ξ k) U)
include hU hξ

theorem ExactVacuumAtlas.Variation.coordChange_shift (ε : ℝ) :
    CoordChange {y | (ε, y) ∈ shiftDom U ξ} U (shiftMap ξ ε) (shiftJac ξ ε) (fun y => (shiftJac ξ ε y)⁻¹) := by sorry
