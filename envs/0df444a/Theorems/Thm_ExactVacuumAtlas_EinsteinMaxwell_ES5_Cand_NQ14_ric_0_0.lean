-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_NQ14_ric_0_0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NQ14.ric_0_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:08:45.255318+00:00
-- url     : https://prove2.me/theorems/5adf19e3-053d-469a-8326-9dd54bd2570f
-- title:
--   NQ14 (ST03 metric with charge 2): Ricci table entry R_{00}
-- statement:
--   NQ14 (ST03 metric with charge 2): Ricci table entry R_{00}
--
--   Generated table lemma for candidate NQ14 (ST03 metric with charge 2): ricciOf gN giN 0 0 x equals the closed form printed in the statement for every x ∈ dom.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选的 Ricci 表项（dom 上）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/NQ14/Ricci.lean#L18-L22; SHA-256 2c6c036db34386d279779b9ffa8d1b6c8a5d518a2ce8d23dce04b132a24641ce. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.NQ14.ric_0_0 (x : Pt 5) (hx : x ∈ dom) :
    ricciOf gN giN 0 0 x = ((12:ℝ) * x 1 ^ 4 + (-24:ℝ) * x 1 ^ 2 + (4:ℝ)) / ((9:ℝ) * x 1 ^ 10) := by sorry
