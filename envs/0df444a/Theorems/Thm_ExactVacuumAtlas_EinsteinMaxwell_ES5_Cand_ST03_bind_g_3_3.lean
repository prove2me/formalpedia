-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_ST03_bind_g_3_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.bind_g_3_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:10:27.044069+00:00
-- url     : https://prove2.me/theorems/d882ca2b-3aaf-4a97-9061-4c57ebbe173d
-- title:
--   ST03 (μ = 2, Q = 1, β = 1/3): binding of g component (3, 3)
-- statement:
--   ST03 (μ = 2, Q = 1, β = 1/3): binding of g component (3, 3)
--
--   For candidate ST03 (μ = 2, Q = 1, β = 1/3): the transcribed candidate component (candG / candGi / candF, according to g) (3, 3) equals the normalised closed form (gN / giN / FN) on dom (Set.EqOn).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选数据分量与规范化闭式在 dom 上相等。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/ST03/Defs.lean#L304-L309; SHA-256 cbbd87aeb4fd4a2e825cc5cbe2c56aaed785af23b07bab33fbae28d77f9c5cc0. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_ST03_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.bind_g_3_3 : Set.EqOn (candG 3 3) (gN 3 3) dom := by sorry
