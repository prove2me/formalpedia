-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_ricci_3_0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.ricci_3_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:47:23.867819+00:00
-- url     : https://prove2.me/theorems/f83c6c52-8250-4cbf-947f-38b0638ec9c9
-- title:
--   KN Ricci component R_{30}
-- statement:
--   KN Ricci component R_{30}
--
--   Closed form of ricciOf (gKN) (giKN) at (3, 0) on domReg.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN Ricci 分量闭式。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Ricci.lean#L145-L159; SHA-256 e817d011c55661ef76e7fc3172a784f05592f4bc47afa248088669235e3c9623. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.ricci_3_0 (x : Pt 4) (hx : x ∈ domReg M a Q) :
    ricciOf (gKN M a Q) (giKN M a Q) 3 0 x = ((2:ℝ) * M * a * Q^2) * (x 1) * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-2:ℝ) * a^3 * Q^2) * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-1:ℝ) * a * Q^4) * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 + ((-2:ℝ) * a * Q^2) * (x 1) ^ 2 * sin (x 2) ^ 2 * Ui a (x 1) (x 2) ^ 3 := by sorry
