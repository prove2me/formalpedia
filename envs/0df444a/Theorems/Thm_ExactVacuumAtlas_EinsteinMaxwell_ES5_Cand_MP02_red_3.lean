-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Cand_MP02_red_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP02.red_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T13:54:47.102057+00:00
-- url     : https://prove2.me/theorems/438f8426-247f-4085-92be-be789e9c347f
-- title:
--   MP02 (μ = 5, rotation constant −2/3): reduced equation number 3 vanishes
-- statement:
--   MP02 (μ = 5, rotation constant −2/3): reduced equation number 3 vanishes
--
--   For candidate MP02 (μ = 5, rotation constant −2/3): reduced equation 3 (0–4: redE_tt, redE_tσ, redE_rr, redE_uu, redE_σσ; 5–6: redJ_t, redJ_σ as printed) of the transcribed radial data vanishes for every r ∈ radR.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 候选的约化方程在 radR 上为零。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Cand/MP02/Reduced.lean#L197-L201; SHA-256 ebf70422c698b70c0b292ddd5a2b49322f1372318f16fdce8cc573907eee782e. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_MP02_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Cand_MP02_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand
open ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Cand.MP02.red_3 (r : ℝ) (hr : r ∈ radR) : Generic.redE_uu rB rD rA rH rW rPhi rPsi r = 0 := by sorry
