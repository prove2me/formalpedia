-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_esInverse_mul
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.esInverse_mul
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:54:04.304977+00:00
-- url     : https://prove2.me/theorems/ea31c748-2a00-46ca-81ae-0965a1cd9a1a
-- title:
--   Equal-spin ansatz: explicit inverse metric
-- statement:
--   Equal-spin ansatz: explicit inverse metric
--
--   For all radial functions B D A H W and x : Pt 5 with B(x 1), D(x 1), A(x 1), H(x 1) ≠ 0 and x 2 ≠ 0, 1 − x 2 ≠ 0: metricMatrix (esInverse B D A H W) x * metricMatrix (esMetric B D A H W) x = 1.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 在 B,D,A,H 非零且 u ≠ 0,1 的点上，esInverse 是 esMetric 的逆矩阵。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Defs.lean#L108-L115; SHA-256 bb9c71fdcb4c409e9bfd1766a9ca9bb3118fe200aee50524ee3c961baaa00f90. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
set_option maxHeartbeats 8000000
variable (B D A H W : ℝ → ℝ)

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.esInverse_mul (x : Pt 5) (hB : B (x 1) ≠ 0) (hD : D (x 1) ≠ 0) (hA : A (x 1) ≠ 0)
    (hH : H (x 1) ≠ 0) (hu : x 2 ≠ 0) (hv : 1 - x 2 ≠ 0) :
    metricMatrix (esInverse B D A H W) x * metricMatrix (esMetric B D A H W) x = 1 := by sorry
