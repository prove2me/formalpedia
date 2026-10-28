-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_eqOn_G4_12_zero
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.eqOn_G4_12_zero
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:46:06.021016+00:00
-- url     : https://prove2.me/theorems/24570c9e-57a6-4346-b610-65ea8083c9aa
-- title:
--   EF5 vanishing Christoffel symbol Γ^{4}_{12}
-- statement:
--   EF5 vanishing Christoffel symbol Γ^{4}_{12}
--
--   For all real μ, β: christoffel (gEF5 μ β) (giEF5 μ β) 4 1 2 = 0 on domU5 (Set.EqOn).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 中恒为零的 Christoffel 符号。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/Ricci.lean#L2765-L2785; SHA-256 f91de831e00ad5d30843158e5baae53dac8ca23c036652f5c758181c627b47f9. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_Defs
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
variable (mu beta : ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.eqOn_G4_12_zero :
    Set.EqOn (christoffel (gEF5 mu beta) (giEF5 mu beta) 4 1 2) (fun _ => 0) domU5 := by sorry
