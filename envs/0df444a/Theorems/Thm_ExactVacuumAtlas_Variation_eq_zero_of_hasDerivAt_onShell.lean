-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_eq_zero_of_hasDerivAt_onShell
-- name    : ExactVacuumAtlas.Variation.eq_zero_of_hasDerivAt_onShell
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:35.552773+00:00
-- url     : https://prove2.me/theorems/653d4733-f992-4f4c-804d-71d61829dc6f
-- title:
--   Derivative of an identically-zero family is zero
-- statement:
--   Derivative of an identically-zero family is zero
--
--   If φ(ε) = 0 whenever (ε, x) ∈ W (open, (0, x) ∈ W) and HasDerivAt φ L 0, then L = 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 恒零族的导数为零。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Bridge.lean#L256-L264; SHA-256 c0401e780ed4e7fdf93b3fceb547d092276cb438ae1a341a5d661c712a8a09c4. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Variation_Defs
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.Variation
variable {n : ℕ}

theorem ExactVacuumAtlas.Variation.eq_zero_of_hasDerivAt_onShell {W : Set (ℝ × Pt n)} (hW : IsOpen W) {x : Pt n}
    (hx : ((0 : ℝ), x) ∈ W) {φ : ℝ → ℝ} {L : ℝ} (hφ : HasDerivAt φ L 0)
    (hz : ∀ ε, (ε, x) ∈ W → φ ε = 0) : L = 0 := by sorry
