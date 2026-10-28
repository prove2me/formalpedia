-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_esInverse_smooth
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.esInverse_smooth
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:54:17.551215+00:00
-- url     : https://prove2.me/theorems/f15c4df3-6f8d-40de-ace5-af1e4d3018cd
-- title:
--   Equal-spin inverse components are C^∞
-- statement:
--   Equal-spin inverse components are C^∞
--
--   If R is open, B, D, A, H, W are C^∞ on R and B, D, A, H ≠ 0 there, every esInverse component is C^∞ on esDomain R (statement as printed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** esInverse 各分量在 esDomain R 上 C^∞。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Defs.lean#L209-L235; SHA-256 bb9c71fdcb4c409e9bfd1766a9ca9bb3118fe200aee50524ee3c961baaa00f90. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.esInverse_smooth {R : Set ℝ} (hB : ContDiffOn ℝ ∞ B R) (hD : ContDiffOn ℝ ∞ D R)
    (hA : ContDiffOn ℝ ∞ A R) (hH : ContDiffOn ℝ ∞ H R) (hW : ContDiffOn ℝ ∞ W R)
    (hB0 : ∀ r ∈ R, B r ≠ 0) (hD0 : ∀ r ∈ R, D r ≠ 0) (hA0 : ∀ r ∈ R, A r ≠ 0)
    (hH0 : ∀ r ∈ R, H r ≠ 0) (i j : Fin 5) :
    ContDiffOn ℝ ∞ (esInverse B D A H W i j) (esDomain R) := by sorry
