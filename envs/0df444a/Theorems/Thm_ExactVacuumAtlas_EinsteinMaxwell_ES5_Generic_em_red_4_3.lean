-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Generic_em_red_4_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.em_red_4_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:04:32.957905+00:00
-- url     : https://prove2.me/theorems/ced98d8b-4157-4aa7-8b1d-7b4abca9c47d
-- title:
--   Residual component E_{43} through the reduced functions
-- statement:
--   Residual component E_{43} through the reduced functions
--
--   Under ESData, for x ∈ esDomain R: einsteinMaxwellD (esMetric …) (esInverse …) (esFaraday …) 4 3 x equals the combination of redE_tt, redE_tσ, redE_rr, redE_uu, redE_σσ at r = x 1 printed in the statement.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 残差分量 E_ab 用五个约化函数表示。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Generic/Reduced.lean#L391-L396; SHA-256 9b826fa37b3eb742414809da83be125f760708c6b7efb905716682ad3dda2820. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.em_red_4_3 (hE : ESData R B D A H W Φ Ψ) (x : Pt 5) (hx : x ∈ (esDomain R)) :
    einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) 4 3 x = ((1:ℝ) * A (x 1) * x 2 ^ 2 + (-1:ℝ) * A (x 1) * x 2) * redE_uu B D A H W Φ Ψ (x 1) + ((-1:ℝ) * H (x 1) * x 2 ^ 2 + (1:ℝ) * H (x 1) * x 2) * redE_σσ B D A H W Φ Ψ (x 1) := by sorry
