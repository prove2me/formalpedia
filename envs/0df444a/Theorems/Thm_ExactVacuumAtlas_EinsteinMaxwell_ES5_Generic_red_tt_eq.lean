-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Generic_red_tt_eq
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.red_tt_eq
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:04:37.064864+00:00
-- url     : https://prove2.me/theorems/676a2680-bfec-493f-95de-66312338c41e
-- title:
--   Reduced function tt as a frame component of the residual
-- statement:
--   Reduced function tt as a frame component of the residual
--
--   Under ESData, for x ∈ esDomain R: the reduced function (tt; ASCII platform names encode σ as _u03c3) at r = x 1 equals the frame contraction of the Einstein–Maxwell residual or Maxwell current printed in the statement (reconstruction lemma).
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 约化函数等于残差/电流的标架分量（重构引理）。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Generic/Reduced.lean#L411-L415; SHA-256 9b826fa37b3eb742414809da83be125f760708c6b7efb905716682ad3dda2820. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
variable {R : Set ℝ} {B D A H W Φ Ψ : ℝ → ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.red_tt_eq (hE : ESData R B D A H W Φ Ψ) (x : Pt 5) (hx : x ∈ (esDomain R)) :
    redE_tt B D A H W Φ Ψ (x 1) = ((-1:ℝ)) / ((1:ℝ) * B (x 1)) * einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) 0 0 x + ((-1:ℝ) * W (x 1)) / ((1:ℝ) * B (x 1)) * einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) 0 3 x + ((-1:ℝ) * W (x 1)) / ((1:ℝ) * B (x 1)) * einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) 0 4 x + ((-1:ℝ) * W (x 1)) / ((1:ℝ) * B (x 1)) * einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) 3 0 x + ((-1:ℝ) * W (x 1) ^ 2) / ((1:ℝ) * B (x 1)) * einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) 3 3 x + ((-1:ℝ) * W (x 1) ^ 2) / ((1:ℝ) * B (x 1)) * einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) 3 4 x + ((-1:ℝ) * W (x 1)) / ((1:ℝ) * B (x 1)) * einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) 4 0 x + ((-1:ℝ) * W (x 1) ^ 2) / ((1:ℝ) * B (x 1)) * einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) 4 3 x + ((-1:ℝ) * W (x 1) ^ 2) / ((1:ℝ) * B (x 1)) * einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) 4 4 x := by sorry
