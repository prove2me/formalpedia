-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_stress_0_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.stress_0_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:47:23.170229+00:00
-- url     : https://prove2.me/theorems/0c0fe5e3-8e34-4999-86d2-6a58389ce77a
-- title:
--   KN Maxwell stress S_{03}
-- statement:
--   KN Maxwell stress S_{03}
--
--   Closed form of emStress at (0, 3) where Σ, Δ, sin θ ≠ 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 电磁应力分量闭式。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Fields.lean#L577-L590; SHA-256 1703a0db2829e50b9c78470ea77810c26f1971c65857e810049e5f3924cca0bd. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_KN_Domain
import Definitions.Def_Atlas_Kerr_InAtoms
open Real
open ExactVacuumAtlas
open scoped ContDiff
open ExactVacuumAtlas.Kerr.In (Ui Wi)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.KN
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (M a Q : ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.stress_0_3 (x : Pt 4) (hS : x 1 ^ 2 + a ^ 2 * cos (x 2) ^ 2 ≠ 0) (hD : x 1 ^ 2 - 2 * M * x 1 + a ^ 2 + Q ^ 2 ≠ 0) (hs : sin (x 2) ≠ 0) :
    emStress (gKN M a Q) (giKN M a Q) (faradayKN a Q) 0 3 x = ((1:ℝ) * M * a * Q^2) * (x 1) * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-1:ℝ) * a^3 * Q^2) * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-1/2:ℝ) * a * Q^4) * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-1:ℝ) * a * Q^2) * (x 1) ^ 2 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 := by sorry
