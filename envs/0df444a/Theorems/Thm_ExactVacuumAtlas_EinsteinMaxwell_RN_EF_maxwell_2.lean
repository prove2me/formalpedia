-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_RN_EF_maxwell_2
-- name    : ExactVacuumAtlas.EinsteinMaxwell.RN.EF.maxwell_2
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:48:55.246306+00:00
-- url     : https://prove2.me/theorems/c6664d35-553d-4975-99b8-b54b1e2dca5f
-- title:
--   RN EF Maxwell residual J^2 = 0
-- statement:
--   RN EF Maxwell residual J^2 = 0
--
--   maxwellDiv (gRN M b) (giRN M b) (faradayRN Q) 2 = 0 on domRN for every real M, b, Q.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** RN EF Maxwell 残差分量为零（任意 b）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/RN/EFFields.lean#L486-L490; SHA-256 bb187e59200833d971df045e4ed8f2a5d42df929974884433ed6a1a38a06f6d5. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Frame
open Real
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.RN
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.RN
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (M b Q : ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.RN.EF.maxwell_2 (x : Pt 4) (hx : x ∈ domRN) :
    maxwellDiv (gRN M b) (giRN M b) (faradayRN Q) 2 x = 0 := by sorry
