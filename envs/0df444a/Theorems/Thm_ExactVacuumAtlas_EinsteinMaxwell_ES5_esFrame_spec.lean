-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_esFrame_spec
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.esFrame_spec
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:54:15.319965+00:00
-- url     : https://prove2.me/theorems/b6ee3cc9-e3d2-40d0-b0e7-701fee58f73d
-- title:
--   Equal-spin frame diagonalises the metric
-- statement:
--   Equal-spin frame diagonalises the metric
--
--   For x with x 2 ≠ 0 and 1 − x 2 ≠ 0: (esFrame W x)ᵀ · esMetric · esFrame W x equals the diagonal matrix printed in the statement.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 等自旋显式标架将度规对角化。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Defs.lean#L134-L141; SHA-256 bb9c71fdcb4c409e9bfd1766a9ca9bb3118fe200aee50524ee3c961baaa00f90. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.esFrame_spec (x : Pt 5) (hu : x 2 ≠ 0) (hv : 1 - x 2 ≠ 0) :
    (esFrame W x).transpose * metricMatrix (esMetric B D A H W) x * esFrame W x =
      Matrix.diagonal ![-B (x 1), D (x 1), A (x 1) / (4 * x 2 * (1 - x 2)), H (x 1),
        A (x 1) * x 2 * (1 - x 2)] := by sorry
