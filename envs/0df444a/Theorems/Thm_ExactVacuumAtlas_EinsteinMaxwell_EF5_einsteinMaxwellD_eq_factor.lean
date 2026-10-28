-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_einsteinMaxwellD_eq_factor
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.einsteinMaxwellD_eq_factor
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:47:16.069586+00:00
-- url     : https://prove2.me/theorems/58347838-ddd1-46e2-b504-31b039404fa8
-- title:
--   EF5: E_ab = (3β − Q²) · emFactorEF5
-- statement:
--   EF5: E_ab = (3β − Q²) · emFactorEF5
--
--   For x ∈ domU5 and all a, b: einsteinMaxwellD … a b x = (3β − Q²) · emFactorEF5 a b x (explicit table; statement as printed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 残差 E_ab = (3β − Q²)·固定因子表。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/EinsteinMaxwellEF5.lean#L659-L688; SHA-256 7d26c41e4b3fd19f383626d85f6a9ed218b2e2f2e7e727ac994cb3ce596b77ed. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.einsteinMaxwellD_eq_factor {x : Pt 5} (hx : x ∈ domU5) (a b : Fin 5) :
    einsteinMaxwellD (gEF5 mu beta) (giEF5 mu beta) (faraday5 Q) a b x =
      (3 * beta - Q ^ 2) * emFactorEF5 mu beta x a b := by sorry
