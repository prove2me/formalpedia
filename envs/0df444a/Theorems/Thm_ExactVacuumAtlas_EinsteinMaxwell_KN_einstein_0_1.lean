-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_einstein_0_1
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.einstein_0_1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:47:21.909633+00:00
-- url     : https://prove2.me/theorems/b82bf1ac-28d2-4129-b1c3-38f262c09636
-- title:
--   KN Einstein residual E_{01} = 0
-- statement:
--   KN Einstein residual E_{01} = 0
--
--   einsteinMaxwell (gKN) (giKN) (faradayKN) 0 1 = 0 on domReg.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN Einstein 残差分量为零。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Einstein.lean#L45-L49; SHA-256 63a254f176601e5da05dba1f10f10a220b1f1056f8d0aa253e2664d1d7518a5e. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.einstein_0_1 (x : Pt 4) (hx : x ∈ domReg M a Q) :
    einsteinMaxwell (gKN M a Q) (giKN M a Q) (faradayKN a Q) 0 1 x = 0 := by sorry
