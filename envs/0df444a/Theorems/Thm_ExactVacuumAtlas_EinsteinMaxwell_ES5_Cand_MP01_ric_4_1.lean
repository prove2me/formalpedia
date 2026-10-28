-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_MP01_ric_4_1
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.ric_4_1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:52:36.518979+00:00
-- url     : https://prove2.me/theorems/70773057-cfc1-48df-9c36-ec09ac67d7c8
-- title:
--   MP01 (μ = 3, a = 1/2): Ricci table entry R_{41}
-- statement:
--   MP01 (μ = 3, a = 1/2): Ricci table entry R_{41}
--
--   Generated table lemma for candidate MP01 (μ = 3, a = 1/2): ricciOf gN giN 4 1 x equals the closed form printed in the statement for every x ∈ dom.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选的 Ricci 表项（dom 上）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/MP01/Ricci.lean#L123-L127; SHA-256 fafc847a176f4ea1b2bce797d2698fe5311d71d504a204b5746ca3c448664b63. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.ric_4_1 (x : Pt 5) (hx : x ∈ dom) :
    ricciOf gN giN 4 1 x = (0:ℝ) := by sorry
