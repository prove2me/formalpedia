-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_pd_g22_u
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.pd_g22_u
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:40:47.375959+00:00
-- url     : https://prove2.me/theorems/ff4f9dd7-7c3c-4370-840b-468ae796ce88
-- title:
--   EF5 metric derivative ∂_u g_{22}
-- statement:
--   EF5 metric derivative ∂_u g_{22}
--
--   For all real μ, β and x ∈ domU5: the derivative in coordinate u of the gEF5 μ β component (2, 2) equals the closed form printed in the statement.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 度规分量的坐标导数。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/Fields.lean#L86-L104; SHA-256 37840e4b53bc8daf733ba7375e17cf627bd160ff9cee97b489d192e051235f22. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.EF5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.EF5
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
variable (mu beta Q : ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.pd_g22_u {x : Pt 5} (hx : x ∈ domU5) :
    pd 2 (gEF5 mu beta 2 2) x = x 1 ^ 2 * (2 * x 2 - 1) / (4 * x 2 ^ 2 * (1 - x 2) ^ 2) := by sorry
