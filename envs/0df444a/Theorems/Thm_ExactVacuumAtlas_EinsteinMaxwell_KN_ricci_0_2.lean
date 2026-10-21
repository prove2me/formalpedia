-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_ricci_0_2
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.ricci_0_2
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:46:14.95408+00:00
-- url     : https://prove2.me/theorems/2f4ba1ec-e9be-4c1d-b3e3-6dc69a9cf040
-- title:
--   KN Ricci component R_{02}
-- statement:
--   KN Ricci component R_{02}
--
--   Closed form of ricciOf (gKN) (giKN) at (0, 2) on domReg.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN Ricci 分量闭式。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Ricci.lean#L45-L49; SHA-256 e817d011c55661ef76e7fc3172a784f05592f4bc47afa248088669235e3c9623. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.ricci_0_2 (x : Pt 4) (hx : x ∈ domReg M a Q) :
    ricciOf (gKN M a Q) (giKN M a Q) 0 2 x = 0 := by sorry
