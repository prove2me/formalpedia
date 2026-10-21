-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_isOpen_shiftDom
-- name    : ExactVacuumAtlas.Variation.isOpen_shiftDom
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:50.667086+00:00
-- url     : https://prove2.me/theorems/18bf4c60-bdd6-477c-9879-c42bcccfb429
-- title:
--   shiftDom is open
-- statement:
--   shiftDom is open
--
--   For open U and C^∞ ξ: shiftDom U ξ ⊆ ℝ × ℝⁿ is open.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** shiftDom 为开集。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Gauge.lean#L103-L114; SHA-256 46d8b5f079abb433286efd867efe3e39da3c640c54b8be946e36e83eaf1a0127. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.isOpen_shiftDom : IsOpen (shiftDom U ξ) := by sorry
