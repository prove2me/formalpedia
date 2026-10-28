-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_ST03_bind_gi_2_2
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.bind_gi_2_2
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:10:52.678197+00:00
-- url     : https://prove2.me/theorems/04976fc6-c8e3-40f5-866e-5ba7544ba6a3
-- title:
--   ST03 (μ = 2, Q = 1, β = 1/3): binding of gi component (2, 2)
-- statement:
--   ST03 (μ = 2, Q = 1, β = 1/3): binding of gi component (2, 2)
--
--   For candidate ST03 (μ = 2, Q = 1, β = 1/3): the transcribed candidate component (candG / candGi / candF, according to gi) (2, 2) equals the normalised closed form (gN / giN / FN) on dom (Set.EqOn).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选数据分量与规范化闭式在 dom 上相等。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/ST03/Defs.lean#L412-L417; SHA-256 cbbd87aeb4fd4a2e825cc5cbe2c56aaed785af23b07bab33fbae28d77f9c5cc0. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.bind_gi_2_2 : Set.EqOn (candGi 2 2) (giN 2 2) dom := by sorry
