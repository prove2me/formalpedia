-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_KN_g_fun_1_1
-- name    : ExactVacuumAtlas.EinsteinMaxwell.KN.g_fun_1_1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:44:30.020905+00:00
-- url     : https://prove2.me/theorems/573b20aa-4a3e-4c0d-a8fc-2e4a38106274
-- title:
--   KN metric component g_{11} as a lifted (r, θ) function
-- statement:
--   KN metric component g_{11} as a lifted (r, θ) function
--
--   gKN M a Q at index (1, 1) equals liftRT of the displayed closed-form expression, rational in r, sin θ and cos θ (with M, a and Q fixed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** KN 度规分量的 (r,θ) 闭式。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/KN/Tables.lean#L46-L51; SHA-256 82a10a4f76cd734d52eeb263411fc37d6c5cd44401612f53bdcd45891d6d7739. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.KN.g_fun_1_1 : gKN M a Q 1 1 = liftRT (fun r θ => ((1:ℝ) * a^2) * cos θ ^ 2 * Di M a Q r + ((1:ℝ)) * r ^ 2 * Di M a Q r) := by sorry
