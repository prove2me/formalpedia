-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_esMetric_lorentz
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.esMetric_lorentz
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:54:28.94216+00:00
-- url     : https://prove2.me/theorems/5536ed38-4f86-4674-8dc5-9cf417728962
-- title:
--   Equal-spin ansatz: Lorentz signature (−,+,+,+,+)
-- statement:
--   Equal-spin ansatz: Lorentz signature (−,+,+,+,+)
--
--   If 0 < A(x 1), 0 < H(x 1), 0 < B(x 1)·D(x 1) and 0 < x 2 < 1, then IsLorentzian (metricMatrix (esMetric B D A H W) x). Both B, D > 0 and B, D < 0 are covered (the sign of B alone is not assumed).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** A>0、H>0、BD>0 且 0<u<1 时 esMetric 为 Lorentz 号差；BD>0 同时覆盖 B,D>0 与 B,D<0 两种情形。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Defs.lean#L152-L175; SHA-256 bb9c71fdcb4c409e9bfd1766a9ca9bb3118fe200aee50524ee3c961baaa00f90. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.esMetric_lorentz (x : Pt 5) (hA : 0 < A (x 1)) (hH : 0 < H (x 1))
    (hBD : 0 < B (x 1) * D (x 1)) (hu : 0 < x 2) (hv : x 2 < 1) :
    IsLorentzian (metricMatrix (esMetric B D A H W) x) := by sorry
