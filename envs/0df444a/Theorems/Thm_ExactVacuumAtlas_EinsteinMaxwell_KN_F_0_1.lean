-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_F_0_1
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.F_0_1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:44:21.570964+00:00
-- url     : https://prove2.me/theorems/7852ce7e-4f03-43d4-9c70-63c17fb583c6
-- title:
--   KN field component F_{01} in rational atoms
-- statement:
--   KN field component F_{01} in rational atoms
--
--   Closed form of faradayKN a Q at index (0, 1) in the atoms Ui = 1/Σ etc., used by the generated KN tables.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 场分量闭式（原子 Ui=1/Σ）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Fields.lean#L102-L106; SHA-256 1703a0db2829e50b9c78470ea77810c26f1971c65857e810049e5f3924cca0bd. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.F_0_1 (x : Pt 4) : faradayKN a Q 0 1 x = ((1:ℝ) * a^2 * Q) * cos (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 2 + ((-1:ℝ) * Q) * (x 1) ^ 2 * Ui a (x 1) (x 2) ^ 2 := by sorry
