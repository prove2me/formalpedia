-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_diagEF5_pos
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.diagEF5_pos
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:41:02.798986+00:00
-- url     : https://prove2.me/theorems/82864b7d-7675-4a7e-98c9-d8eebc0984da
-- title:
--   EF5 frame: spatial diagonal entries are positive
-- statement:
--   EF5 frame: spatial diagonal entries are positive
--
--   For x ∈ domU5 and i ≠ 0: 0 < diagEF5 μ β x i.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 标架对角元（i≠0）为正。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/Frame.lean#L97-L110; SHA-256 ebaa68d722fd05664bf7ac50f56351f249f3836d963a5684a125adab0dff5509. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_EF5_Frame
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.EF5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.EF5
set_option maxHeartbeats 4000000

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.diagEF5_pos (mu beta : ℝ) {x : Pt 5} (hx : x ∈ domU5) :
    ∀ i, i ≠ 0 → 0 < diagEF5 mu beta x i := by sorry
