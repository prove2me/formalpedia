-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_NQ14_rH_eq
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NQ14.rH_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:07:14.154343+00:00
-- url     : https://prove2.me/theorems/3a55a351-0407-4c26-b01c-617ff87b4152
-- title:
--   NQ14 (ST03 metric with charge 2): closed form of the radial function rH
-- statement:
--   NQ14 (ST03 metric with charge 2): closed form of the radial function rH
--
--   For candidate NQ14 (ST03 metric with charge 2): for every r ∈ radR, the transcribed radial function rH equals the factored closed form printed in the statement (factor polynomials f… are opaque names).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选径向函数在 radR 上的因式化闭式。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/NQ14/Defs.lean#L128-L134; SHA-256 414b38f26c883112e2d1e08ed57a5a8b68ed097c41c3b20cf6eb280987bfac30. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_NQ14_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NQ14
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NQ14.rH_eq (r : ℝ) (hr : r ∈ radR) : rH r = ((1:ℝ) * r ^ 2) := by sorry
