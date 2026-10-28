-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_ricciOf_eq_table
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.ricciOf_eq_table
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:47:20.209501+00:00
-- url     : https://prove2.me/theorems/df0438cf-11cd-4f49-b3a2-a0ffdd8db4e4
-- title:
--   EF5: all 25 Ricci components equal the closed-form table
-- statement:
--   EF5: all 25 Ricci components equal the closed-form table
--
--   For x ∈ domU5 and all a, b: ricciOf (gEF5 μ β) (giEF5 μ β) a b x = ricciTableEF5 μ β a b x.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 的 25 个 Ricci 分量等于闭式表。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/RicciOffDiag.lean#L1024-L1052; SHA-256 c83cc0a4d094e8f13b4bd785a9b026d4c4a78c138662ba4ab44510d8cc4b331c. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.ricciOf_eq_table {x : Pt 5} (hx : x ∈ domU5) (a b : Fin 5) :
    ricciOf (gEF5 mu beta) (giEF5 mu beta) a b x = ricciTableEF5 mu beta x a b := by sorry
