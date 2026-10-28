-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_ST03_bind_F_4_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.bind_F_4_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:10:47.052555+00:00
-- url     : https://prove2.me/theorems/3446ad81-0e52-4a96-91c9-90c2ab90ae8a
-- title:
--   ST03 (μ = 2, Q = 1, β = 1/3): binding of F component (4, 3)
-- statement:
--   ST03 (μ = 2, Q = 1, β = 1/3): binding of F component (4, 3)
--
--   For candidate ST03 (μ = 2, Q = 1, β = 1/3): the transcribed candidate component (candG / candGi / candF, according to F) (4, 3) equals the normalised closed form (gN / giN / FN) on dom (Set.EqOn).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选数据分量与规范化闭式在 dom 上相等。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/ST03/EM.lean#L323-L328; SHA-256 e0e60237c0097c06dfd2e757f628aafa120768f0ae611b948d8b10f9d88cbebb. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_ST03_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_ST03_EM
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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.bind_F_4_3 : Set.EqOn (candF 4 3) (FN 4 3) dom := by sorry
