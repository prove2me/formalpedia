-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_ricci_04
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.ricci_04
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:47:06.815951+00:00
-- url     : https://prove2.me/theorems/5d91e776-0f5e-41f6-8e44-5114da0dd8e8
-- title:
--   EF5 Ricci component R_{04}
-- statement:
--   EF5 Ricci component R_{04}
--
--   For all real μ, β and x ∈ domU5: ricciOf (gEF5 μ β) (giEF5 μ β) 0 4 x equals the closed form printed in the statement.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 Ricci 分量闭式。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/RicciOffDiag.lean#L860-L865; SHA-256 c83cc0a4d094e8f13b4bd785a9b026d4c4a78c138662ba4ab44510d8cc4b331c. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_RicciOffDiag
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.EF5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.EF5
set_option maxHeartbeats 400000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
variable (mu beta : ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.ricci_04 {x : Pt 5} (hx : x ∈ domU5) :
    ricciOf (gEF5 mu beta) (giEF5 mu beta) 0 4 x = 0 := by sorry
