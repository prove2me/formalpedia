-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_fieldSq_ef5
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.fieldSq_ef5
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:40:50.872036+00:00
-- url     : https://prove2.me/theorems/5a902ec5-644b-49df-8f97-da60207c53a6
-- title:
--   EF5: field invariant F_ab F^ab = −2Q²/r⁶
-- statement:
--   EF5: field invariant F_ab F^ab = −2Q²/r⁶
--
--   For all real μ, β, Q and x: fieldSq (giEF5 μ β) (faraday5 Q) x = −2Q²/(x 1)⁶ (statement as printed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 场不变量 F_ab F^ab = −2Q²/r⁶。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/EinsteinMaxwellEF5.lean#L274-L278; SHA-256 7d26c41e4b3fd19f383626d85f6a9ed218b2e2f2e7e727ac994cb3ce596b77ed. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.fieldSq_ef5 (x : Pt 5) :
    fieldSq (giEF5 mu beta) (faraday5 Q) x = -2 * Q ^ 2 / x 1 ^ 6 := by sorry
