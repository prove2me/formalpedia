-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_EF5_frameEF5_diag_spec
-- name    : ExactVacuumAtlas.EinsteinMaxwell.EF5.frameEF5_diag_spec
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:47:51.855982+00:00
-- url     : https://prove2.me/theorems/1edb98f4-a568-4179-b257-e8473e2d365f
-- title:
--   EF5 frame diagonalises the metric
-- statement:
--   EF5 frame diagonalises the metric
--
--   For x ∈ domU5: Eᵀ g E = diagonal(diagEF5 μ β x) for E = frameEF5 μ β (diag = (−1, 1, r²/(4u(1−u)), r²u, r²(1−u))).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** EF5 显式标架将度规对角化。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/EF5/Frame.lean#L71-L90; SHA-256 ebaa68d722fd05664bf7ac50f56351f249f3836d963a5684a125adab0dff5509. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.EF5.frameEF5_diag_spec (mu beta : ℝ) {x : Pt 5} (hx : x ∈ domU5) :
    (metricMatrix (frameEF5 mu beta) x).transpose * metricMatrix (gEF5 mu beta) x *
      metricMatrix (frameEF5 mu beta) x = Matrix.diagonal (diagEF5 mu beta x) := by sorry
