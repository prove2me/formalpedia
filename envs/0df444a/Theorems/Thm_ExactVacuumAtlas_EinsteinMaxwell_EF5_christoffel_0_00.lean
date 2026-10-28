-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_christoffel_0_00
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.christoffel_0_00
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:40:39.502099+00:00
-- url     : https://prove2.me/theorems/b1dd44a6-7fe1-456f-9f9c-e818fea3b5a3
-- title:
--   EF5 Christoffel symbol Γ^{0}_{00}
-- statement:
--   EF5 Christoffel symbol Γ^{0}_{00}
--
--   For all real μ, β and x ∈ domU5: christoffel (gEF5 μ β) (giEF5 μ β) 0 0 0 x equals the closed form printed in the statement.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 Christoffel 符号的闭式（domU5 上）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/Christoffel.lean#L251-L260; SHA-256 90fe25de2f82753591f0b50b0cfdaf5a2c47dedad5dda3c9dd463afe9ffca4e1. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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
set_option maxHeartbeats 80000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
variable (mu beta : ℝ) (x : Pt 5)

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.christoffel_0_00 (mu beta : ℝ) {x : Pt 5} (hx : x ∈ domU5) :
    christoffel (gEF5 mu beta) (giEF5 mu beta) 0 0 0 x =
    mu / x 1 ^ 3 - 2 * beta / x 1 ^ 5 := by sorry
