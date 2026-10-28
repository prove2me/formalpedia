-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_pd_r_G1_22
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.pd_r_G1_22
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:45:18.690004+00:00
-- url     : https://prove2.me/theorems/03aac96a-8a69-4229-9f19-e7aa64e9110c
-- title:
--   EF5 derivative ∂_r Γ^{1}_{22}
-- statement:
--   EF5 derivative ∂_r Γ^{1}_{22}
--
--   For all real μ, β and x ∈ domU5: the coordinate derivative (pd, coordinate r) of christoffel (gEF5 μ β) (giEF5 μ β) 1 2 2 equals the closed form printed in the statement.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 Christoffel 符号的坐标导数闭式。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/Ricci.lean#L306-L334; SHA-256 f91de831e00ad5d30843158e5baae53dac8ca23c036652f5c758181c627b47f9. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.pd_r_G1_22 {x : Pt 5} (hx : x ∈ domU5) :
    pd 1 (christoffel (gEF5 mu beta) (giEF5 mu beta) 1 2 2) x =
    -(1 + mu / x 1 ^ 2 - 3 * beta / x 1 ^ 4) / (4 * x 2 * (1 - x 2)) := by sorry
