-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_pd_eq_zero_of_eqOn_indep
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.pd_eq_zero_of_eqOn_indep
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:46:04.124371+00:00
-- url     : https://prove2.me/theorems/cc1a4b69-153a-4646-bfbc-969735432114
-- title:
--   Partial derivative of a function equal on domU5 to one independent of a coordinate
-- statement:
--   Partial derivative of a function equal on domU5 to one independent of a coordinate
--
--   If f = h on domU5, x ∈ domU5 and h does not depend on coordinate i, then pd i f x = 0.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 在 domU5 上等于与某坐标无关的函数时，该坐标偏导为零。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/RicciOffDiag.lean#L24-L30; SHA-256 c83cc0a4d094e8f13b4bd785a9b026d4c4a78c138662ba4ab44510d8cc4b331c. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_Defs
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
variable (mu beta : ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.pd_eq_zero_of_eqOn_indep {f h : Pt 5 → ℝ} {x : Pt 5} (hx : x ∈ domU5)
    (hfh : Set.EqOn f h domU5) (i : Fin 5)
    (hind : ∀ t : ℝ, h (Function.update x i t) = h x) : pd i f x = 0 := by sorry
