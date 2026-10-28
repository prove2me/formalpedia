-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_raise2_ef5_43
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.raise2_ef5_43
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:41:19.128245+00:00
-- url     : https://prove2.me/theorems/953c0635-2bcc-4a3e-9466-9d9040bffc9b
-- title:
--   EF5 raised field component F^{43}
-- statement:
--   EF5 raised field component F^{43}
--
--   For all real μ, β, Q: raise2 (giEF5 μ β) (faraday5 Q) 4 3 equals the function printed in the statement.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 上指标场强分量。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/EinsteinMaxwellEF5.lean#L261-L266; SHA-256 7d26c41e4b3fd19f383626d85f6a9ed218b2e2f2e7e727ac994cb3ce596b77ed. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_EinsteinMaxwellEF5
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
set_option linter.unreachableTactic false
variable (mu beta Q : ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.raise2_ef5_43 :
    raise2 (giEF5 mu beta) (faraday5 Q) 4 3 = fun _ => 0 := by sorry
