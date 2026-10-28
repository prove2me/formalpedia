-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_MP01_em_0_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.em_0_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:52:38.560978+00:00
-- url     : https://prove2.me/theorems/1d49f989-3781-4915-8124-99e99c514be8
-- title:
--   MP01 (μ = 3, a = 1/2): Einstein–Maxwell table entry E_{03}
-- statement:
--   MP01 (μ = 3, a = 1/2): Einstein–Maxwell table entry E_{03}
--
--   Generated table lemma for candidate MP01 (μ = 3, a = 1/2): einsteinMaxwellD gN giN FN 0 3 x equals the closed form printed in the statement for every x ∈ dom.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选的 Einstein–Maxwell 残差表项（dom 上）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/MP01/EM.lean#L1357-L1361; SHA-256 455a652cff7eba5d84e372851b49f3195a5f296c8a464a2f2a34d04d1a5c84bb. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_MP01_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_MP01_EM
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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.em_0_3 (x : Pt 5) (hx : x ∈ dom) :
    einsteinMaxwellD gN giN FN 0 3 x = (0:ℝ) := by sorry
