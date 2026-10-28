-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_ST03_ric_0_0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.ric_0_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:14:56.15664+00:00
-- url     : https://prove2.me/theorems/7fb5a7fe-0439-4e25-b542-5e0251a691f9
-- title:
--   ST03 (μ = 2, Q = 1, β = 1/3): Ricci table entry R_{00}
-- statement:
--   ST03 (μ = 2, Q = 1, β = 1/3): Ricci table entry R_{00}
--
--   Generated table lemma for candidate ST03 (μ = 2, Q = 1, β = 1/3): ricciOf gN giN 0 0 x equals the closed form printed in the statement for every x ∈ dom.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选的 Ricci 表项（dom 上）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/ST03/Ricci.lean#L18-L22; SHA-256 86db6332714afbbad4c6e388da746d634a19772f0b005f4dd8a7442df867b4cf. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.ST03.ric_0_0 (x : Pt 5) (hx : x ∈ dom) :
    ricciOf gN giN 0 0 x = ((12:ℝ) * x 1 ^ 4 + (-24:ℝ) * x 1 ^ 2 + (4:ℝ)) / ((9:ℝ) * x 1 ^ 10) := by sorry
