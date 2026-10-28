-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_MP01_dg_3_3_1
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.dg_3_3_1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:50:42.332603+00:00
-- url     : https://prove2.me/theorems/9a945255-8287-4ffe-88eb-d0ec42049027
-- title:
--   MP01 (μ = 3, a = 1/2): metric derivative ∂_1 g_{33}
-- statement:
--   MP01 (μ = 3, a = 1/2): metric derivative ∂_1 g_{33}
--
--   Generated table lemma for candidate MP01 (μ = 3, a = 1/2): pd 1 (gN 3 3) x equals the expression printed in the statement for every x ∈ dom.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选度规表项的坐标导数。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/MP01/Chr.lean#L279-L283; SHA-256 579852ad501dc5fb127d39ea1568832e6df93c261cf0e4bd33e2fe75f3430707. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP01.dg_3_3_1 (x : Pt 5) (hx : x ∈ dom) :
    pd 1 (gN 3 3) x = ((32:ℝ) * x 1 ^ 5 * x 2 + (16:ℝ) * x 1 ^ 3 * x 2 + (-24:ℝ) * x 1 * x 2 ^ 2 + (2:ℝ) * x 1 * x 2) / ((1:ℝ) * fS (x 1) ^ 2) := by sorry
