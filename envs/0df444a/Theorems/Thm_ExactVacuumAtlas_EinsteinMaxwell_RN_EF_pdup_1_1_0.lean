-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_RN_EF_pdup_1_1_0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.RN.EF.pdup_1_1_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:49:22.40557+00:00
-- url     : https://prove2.me/theorems/3505e197-8e93-4e20-81f4-0d859e9ad463
-- title:
--   RN EF derivative ∂_1 F^{10}
-- statement:
--   RN EF derivative ∂_1 F^{10}
--
--   Closed form of pd 1 (raise2 (giRN M b) (faradayRN Q) 1 0) on domRN.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** RN EF 升指标场的偏导闭式。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/RN/EFFields.lean#L269-L273; SHA-256 bb187e59200833d971df045e4ed8f2a5d42df929974884433ed6a1a38a06f6d5. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.RN.EF.pdup_1_1_0 (x : Pt 4) (hx : x ∈ domRN) :
    pd 1 (raise2 (giRN M b) (faradayRN Q) 1 0) x = -2 * (-Q) / (x 1) ^ 3 := by sorry
