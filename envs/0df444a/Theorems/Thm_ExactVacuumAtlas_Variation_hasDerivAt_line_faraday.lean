-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_hasDerivAt_line_faraday
-- name    : ExactVacuumAtlas.Variation.hasDerivAt_line_faraday
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:43.655115+00:00
-- url     : https://prove2.me/theorems/7a51a26a-c2c7-40d9-a524-756b58e8b5dc
-- title:
--   Derivative of the H residual along the straight-line family
-- statement:
--   Derivative of the H residual along the straight-line family
--
--   For open U ⊆ ℝ⁴, C^∞ g, F, h, f on U, a true inverse gi of g on U (gi · g = 1) and x ∈ U: the ε-derivative at 0 of the H residual of (g + εh, (g + εh)⁻¹, F + εf) at x is the corresponding linearised operator evaluated at (g, gi, F; h, f).
--
--   **Scope.** Any C^∞ (h, f) depending on all coordinates; background need not satisfy any equation; local in x.
--
--   **中文摘要** 沿直线族的 H 残差在 ε=0 的真实导数等于对应线性化算子。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/LineFamily.lean#L120-L123; SHA-256 afc3b70a17a93bd1217b6ce19d567cf12c2c04fac9d9ce907ceab23c88c02112. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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
variable {U : Set (Pt 4)} {g gi h : Metric 4} {F f : TwoForm 4}
  (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (g i j) U)
  (hinv : ∀ y ∈ U, metricMatrix gi y * metricMatrix g y = 1) (hF : ∀ i j, ContDiffOn ℝ ∞ (F i j) U)
  (hh : ∀ i j, ContDiffOn ℝ ∞ (h i j) U) (hf : ∀ i j, ContDiffOn ℝ ∞ (f i j) U)
include hU hg hinv hF hh hf

theorem ExactVacuumAtlas.Variation.hasDerivAt_line_faraday {x : Pt 4} (hx : x ∈ U) (a b c : Fin 4) :
    HasDerivAt (fun ε => faradayCyclic (lineMetric F f ε) a b c x) (linFaraday f a b c x) 0 := by sorry
