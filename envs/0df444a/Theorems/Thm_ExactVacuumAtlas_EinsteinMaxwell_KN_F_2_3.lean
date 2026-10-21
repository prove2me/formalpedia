-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_F_2_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.F_2_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:44:17.98452+00:00
-- url     : https://prove2.me/theorems/fd4eae16-f79e-4f02-acdb-ad36e2331c8e
-- title:
--   KN field component F_{23} in rational atoms
-- statement:
--   KN field component F_{23} in rational atoms
--
--   Closed form of faradayKN a Q at index (2, 3) in the atoms Ui = 1/Σ etc., used by the generated KN tables.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 场分量闭式（原子 Ui=1/Σ）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Fields.lean#L132-L136; SHA-256 1703a0db2829e50b9c78470ea77810c26f1971c65857e810049e5f3924cca0bd. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.F_2_3 (x : Pt 4) : faradayKN a Q 2 3 x = ((2:ℝ) * a^3 * Q) * (x 1) * sin (x 2) * cos (x 2) * Ui a (x 1) (x 2) ^ 2 + ((2:ℝ) * a * Q) * (x 1) ^ 3 * sin (x 2) * cos (x 2) * Ui a (x 1) (x 2) ^ 2 := by sorry
