-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Generic_fu_on_3_2
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.fu_on_3_2
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:02:52.275193+00:00
-- url     : https://prove2.me/theorems/0fd7c178-caa7-4cbf-a642-704c777a66f1
-- title:
--   Generic raised field table entry F^{32}
-- statement:
--   Generic raised field table entry F^{32}
--
--   Under ESData: raise2 (giG …) (FG …) 3 2 equals the explicit expression printed in the statement on esDomain R (Set.EqOn).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 一般拟设上指标场强表项。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Generic/EM.lean#L122-L127; SHA-256 c2a580eeb69d9fe80afdff3d4b529ab4e4c848628f5a8a415390c9b8dffcdb8b. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.fu_on_3_2 (hE : ESData R B D A H W Φ Ψ) :
    Set.EqOn (raise2 (giG B D A H W) (FG Φ Ψ) 3 2) (liftRU (fun r u => ((4:ℝ) * Ψ r * u + (-4:ℝ) * Ψ r) / ((1:ℝ) * A r ^ 2) : ℝ → ℝ → ℝ)) (esDomain R) := by sorry
