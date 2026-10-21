-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_familyData_line
-- name    : ExactVacuumAtlas.Variation.familyData_line
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:51:18.302069+00:00
-- url     : https://prove2.me/theorems/3a554bea-1457-4e9a-af25-98cf502d350a
-- title:
--   Every C^∞ direction is realised by a genuine local straight-line family
-- statement:
--   Every C^∞ direction is realised by a genuine local straight-line family
--
--   For any n, open U ⊆ ℝⁿ and C^∞ (on U) component fields g, h (Metric n) and F, f (TwoForm n): the family ε ↦ (g + εh, (g + εh)⁻¹, F + εf), with (g + εh)⁻¹ the Mathlib matrix inverse, satisfies FamilyData on lineDom U g h = {(ε, y) : y ∈ U, det(g + εh)(y) ≠ 0}.
--
--   **Scope.** Local: lineDom is open but no uniform ε-interval over a non-compact U is claimed; (0, x) ∈ lineDom iff x ∈ U and det g(x) ≠ 0. h, f may depend on all four coordinates; no symmetry or field equation is assumed. Combined with the goal bridge this gives the derivatives along the line (hasDerivAt_line_*). The family is not claimed to consist of solutions.
--
--   **中文摘要** 任意 C^∞ 的 (h,f) 都由真实的直线族 g+εh、(g+εh)⁻¹、F+εf 在开集 lineDom 上实现为 FamilyData。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/LineFamily.lean#L64-L74; SHA-256 afc3b70a17a93bd1217b6ce19d567cf12c2c04fac9d9ce907ceab23c88c02112. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_LineFamily
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Local
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}
variable {U : Set (Pt n)} {g gi h : Metric n} {F f : TwoForm n}

theorem ExactVacuumAtlas.Variation.familyData_line (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (g i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (h i j) U) (hF : ∀ i j, ContDiffOn ℝ ∞ (F i j) U)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (f i j) U) :
    FamilyData (lineMetric g h) (lineInv g h) (lineMetric F f) (lineDom U g h) := by sorry
