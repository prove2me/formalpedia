-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_MP01_bind_g_2_2
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.bind_g_2_2
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:49:31.126447+00:00
-- url     : https://prove2.me/theorems/c22138fc-9f1f-4f27-bb77-ded60b0eec0b
-- title:
--   MP01 (μ = 3, a = 1/2): binding of g component (2, 2)
-- statement:
--   MP01 (μ = 3, a = 1/2): binding of g component (2, 2)
--
--   For candidate MP01 (μ = 3, a = 1/2): the transcribed candidate component (candG / candGi / candF, according to g) (2, 2) equals the normalised closed form (gN / giN / FN) on dom (Set.EqOn).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选数据分量与规范化闭式在 dom 上相等。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/MP01/Defs.lean#L310-L315; SHA-256 5e312fea99565a4d89b7e21bb975047b15693166f96fa9be22c1fff2a8445421. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.bind_g_2_2 : Set.EqOn (candG 2 2) (gN 2 2) dom := by sorry
