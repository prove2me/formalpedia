-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_linearized_potential_gauge_eq_zero
-- name    : ExactVacuumAtlas.Variation.linearized_potential_gauge_eq_zero
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:51:51.026987+00:00
-- url     : https://prove2.me/theorems/bdf91f0f-a5e9-480b-8de6-0f4da38da269
-- title:
--   Potential gauge directions δA = dχ solve the linearised equations
-- statement:
--   Potential gauge directions δA = dχ solve the linearised equations
--
--   For open U ⊆ ℝ⁴, C^∞ χ on U, ANY g, gi, F and x ∈ U, with h = 0 and f = extD (gradCo χ) = d(dχ): LE_ab = 0, LJ^b = 0, LH_abc = 0 at x.
--
--   **Scope.** f = d(dχ) vanishes on U for C^∞ χ (extD_gradCo, symmetry of second derivatives), so no certificate is needed. This is the electromagnetic potential gauge only; it is neither the coordinate gauge nor an NP phantom gauge.
--
--   **中文摘要** 势规范方向 δA = dχ（h=0，f=d(dχ)）对任意背景给出零线性化残差。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Gauge.lean#L327-L344; SHA-256 46d8b5f079abb433286efd867efe3e39da3c640c54b8be946e36e83eaf1a0127. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.Variation.linearized_potential_gauge_eq_zero {U : Set (Pt 4)} (hU : IsOpen U) {χ : Pt 4 → ℝ}
    (hχ : ContDiffOn ℝ ∞ χ U) (g gi : Metric 4) (F : TwoForm 4) {x : Pt 4} (hx : x ∈ U) :
    (∀ a b, linEinstein g gi F 0 (extD (gradCo χ)) a b x = 0) ∧
    (∀ b, linMaxwell g gi F 0 (extD (gradCo χ)) b x = 0) ∧
    (∀ a b c, linFaraday (extD (gradCo χ)) a b c x = 0) := by sorry
