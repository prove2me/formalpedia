-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_inv_mul_EF5
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.inv_mul_EF5
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:47:31.603863+00:00
-- url     : https://prove2.me/theorems/57725307-cbfe-4826-86d5-695568747a7c
-- title:
--   EF5: explicit inverse
-- statement:
--   EF5: explicit inverse
--
--   For all real μ, β and x ∈ domU5: metricMatrix (giEF5 μ β) x * metricMatrix (gEF5 μ β) x = 1.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 显式逆度规。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/Defs.lean#L62-L69; SHA-256 f231f4a9949f874f4e55d1d1a5d115dc989dd2dea043b61580e11ec6dcfcc0ca. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.EF5
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.inv_mul_EF5 (mu beta : ℝ) {x : Pt 5} (hx : x ∈ domU5) :
    metricMatrix (giEF5 mu beta) x * metricMatrix (gEF5 mu beta) x = 1 := by sorry
