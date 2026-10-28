-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Generic_bind_g_4_0
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.bind_g_4_0
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:58:59.200759+00:00
-- url     : https://prove2.me/theorems/05aab8b8-5fd3-4a71-be1a-f975953684e5
-- title:
--   Generic binding of g component (4, 0)
-- statement:
--   Generic binding of g component (4, 0)
--
--   Under ESData R B D A H W Φ Ψ: the component of esMetric / esInverse / esFaraday (according to g) at (4, 0) equals the normalised table gG / giG / FG on esDomain R (Set.EqOn).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 一般拟设：esMetric/esInverse/esFaraday 分量与规范化表在 esDomain R 上相等。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Generic/Tables.lean#L184-L189; SHA-256 0b8e01dc10c5b67eb7077e8a1630f890465fbae34c4775d6930d2f09bf7ef196. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.bind_g_4_0 (hE : ESData R B D A H W Φ Ψ) :
    Set.EqOn (esMetric B D A H W 4 0) (gG B D A H W 4 0) (esDomain R) := by sorry
