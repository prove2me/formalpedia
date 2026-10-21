-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_RN_EF_ricci_0_0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.RN.EF.ricci_0_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:48:47.486505+00:00
-- url     : https://prove2.me/theorems/7c7e0e01-cea4-43b3-973d-fad39f88c0bf
-- title:
--   RN EF Ricci component R_{00}
-- statement:
--   RN EF Ricci component R_{00}
--
--   Closed form of ricciOf (gRN M b) (giRN M b) at (0, 0) on domRN, for every real b.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** RN EF Ricci 分量闭式（任意 b）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/RN/EFTables.lean#L1571-L1577; SHA-256 357665b31cd7a1216ed99e3ed471e28bd4f147930744b8837a0c9f3507a75f0c. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Lift
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_RN_Defs
open Real
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.RN
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.RN
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (M b : ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.RN.EF.ricci_0_0 (x : Pt 4) (hx : x ∈ domRN)   :
    ricciOf (gRN M b) (giRN M b) 0 0 x = (1 - 2*M/(x 1) + b/(x 1)^2) * b / (x 1)^4 := by sorry
