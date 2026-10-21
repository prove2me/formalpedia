-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_maxwell_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.maxwell_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:48:40.917976+00:00
-- url     : https://prove2.me/theorems/2643ebea-8b76-4322-a42f-dd4df78ee2f6
-- title:
--   KN Maxwell residual J^3 = 0
-- statement:
--   KN Maxwell residual J^3 = 0
--
--   maxwellDiv (gKN) (giKN) (faradayKN) 3 = 0 on domReg.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN Maxwell 残差分量为零。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Fields.lean#L724-L738; SHA-256 1703a0db2829e50b9c78470ea77810c26f1971c65857e810049e5f3924cca0bd. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.maxwell_3 (x : Pt 4) (hx : x ∈ domReg M a Q) :
    maxwellDiv (gKN M a Q) (giKN M a Q) (faradayKN a Q) 3 x = 0 := by sorry
