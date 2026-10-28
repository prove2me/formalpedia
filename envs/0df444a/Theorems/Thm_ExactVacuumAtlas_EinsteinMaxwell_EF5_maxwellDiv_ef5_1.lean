-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_maxwellDiv_ef5_1
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.maxwellDiv_ef5_1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:47:18.236864+00:00
-- url     : https://prove2.me/theorems/b4aa4652-7bf6-44e2-94d9-cb6bc2f4b1ba
-- title:
--   EF5 Maxwell divergence component J^1
-- statement:
--   EF5 Maxwell divergence component J^1
--
--   For all real μ, β, Q and x ∈ domU5: maxwellDiv (gEF5 μ β) (giEF5 μ β) (faraday5 Q) 1 x equals the value printed in the statement.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 Maxwell 散度分量。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/EinsteinMaxwellEF5.lean#L303-L310; SHA-256 7d26c41e4b3fd19f383626d85f6a9ed218b2e2f2e7e727ac994cb3ce596b77ed. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_EinsteinMaxwellEF5
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_RicciOffDiag
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.EF5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.EF5
set_option maxHeartbeats 400000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable (mu beta Q : ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.maxwellDiv_ef5_1 {x : Pt 5} (hx : x ∈ domU5) :
    maxwellDiv (gEF5 mu beta) (giEF5 mu beta) (faraday5 Q) 1 x = 0 := by sorry
