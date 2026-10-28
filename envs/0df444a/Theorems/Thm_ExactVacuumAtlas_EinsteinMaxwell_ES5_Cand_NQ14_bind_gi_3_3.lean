-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_NQ14_bind_gi_3_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NQ14.bind_gi_3_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:08:11.072365+00:00
-- url     : https://prove2.me/theorems/1999639c-47e4-4b3a-ab73-1835318a4f83
-- title:
--   NQ14 (ST03 metric with charge 2): binding of gi component (3, 3)
-- statement:
--   NQ14 (ST03 metric with charge 2): binding of gi component (3, 3)
--
--   For candidate NQ14 (ST03 metric with charge 2): the transcribed candidate component (candG / candGi / candF, according to gi) (3, 3) equals the normalised closed form (gN / giN / FN) on dom (Set.EqOn).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选数据分量与规范化闭式在 dom 上相等。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/NQ14/Defs.lean#L444-L449; SHA-256 414b38f26c883112e2d1e08ed57a5a8b68ed097c41c3b20cf6eb280987bfac30. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NQ14.bind_gi_3_3 : Set.EqOn (candGi 3 3) (giN 3 3) dom := by sorry
