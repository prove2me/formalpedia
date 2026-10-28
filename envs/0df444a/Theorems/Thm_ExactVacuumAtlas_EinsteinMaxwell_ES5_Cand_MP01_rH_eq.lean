-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_MP01_rH_eq
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.rH_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:49:05.895394+00:00
-- url     : https://prove2.me/theorems/0afbc04f-b597-4a13-ba8f-a4f3ed2fd33e
-- title:
--   MP01 (μ = 3, a = 1/2): closed form of the radial function rH
-- statement:
--   MP01 (μ = 3, a = 1/2): closed form of the radial function rH
--
--   For candidate MP01 (μ = 3, a = 1/2): for every r ∈ radR, the transcribed radial function rH equals the factored closed form printed in the statement (factor polynomials f… are opaque names).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选径向函数在 radR 上的因式化闭式。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/MP01/Defs.lean#L150-L157; SHA-256 5e312fea99565a4d89b7e21bb975047b15693166f96fa9be22c1fff2a8445421. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_MP01_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.rH_eq (r : ℝ) (hr : r ∈ radR) : rH r = ((1/4:ℝ) * fP r / (fS r)) := by sorry
