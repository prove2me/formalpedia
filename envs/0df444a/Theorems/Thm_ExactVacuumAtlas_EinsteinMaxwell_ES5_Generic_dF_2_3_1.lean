-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Generic_dF_2_3_1
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.dF_2_3_1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:57:37.715269+00:00
-- url     : https://prove2.me/theorems/cb1f950b-9d22-4955-b6d8-65c46f4a31ff
-- title:
--   Generic field-strength derivative ∂_1 F_{23}
-- statement:
--   Generic field-strength derivative ∂_1 F_{23}
--
--   Under ESData, for x ∈ esDomain R: pd 1 (FG Φ Ψ 2 3) x equals the expression printed in the statement.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 一般拟设场强表项的坐标导数。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Generic/EM.lean#L455-L459; SHA-256 c2a580eeb69d9fe80afdff3d4b529ab4e4c848628f5a8a415390c9b8dffcdb8b. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable {R : Set ℝ} {B D A H W Φ Ψ : ℝ → ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.dF_2_3_1 (hE : ESData R B D A H W Φ Ψ) (x : Pt 5) (hx : x ∈ (esDomain R)) :
    pd 1 (FG Φ Ψ 2 3) x = ((1:ℝ) * deriv Ψ (x 1)) := by sorry
