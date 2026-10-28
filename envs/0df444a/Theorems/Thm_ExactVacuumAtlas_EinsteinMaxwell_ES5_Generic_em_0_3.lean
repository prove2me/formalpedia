-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Generic_em_0_3
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.em_0_3
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:04:08.468742+00:00
-- url     : https://prove2.me/theorems/4414af8d-6be7-4975-a935-d943e9bdbc19
-- title:
--   Generic Einstein–Maxwell table entry E_{03}
-- statement:
--   Generic Einstein–Maxwell table entry E_{03}
--
--   Under ESData R B D A H W Φ Ψ, for x ∈ esDomain R: einsteinMaxwellD (gG …) (giG …) (FG …) 0 3 x equals the expression in the radial jets printed in the statement.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 一般拟设的 Einstein–Maxwell 残差表项。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Generic/EM.lean#L1290-L1294; SHA-256 c2a580eeb69d9fe80afdff3d4b529ab4e4c848628f5a8a415390c9b8dffcdb8b. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.em_0_3 (hE : ESData R B D A H W Φ Ψ) (x : Pt 5) (hx : x ∈ (esDomain R)) :
    einsteinMaxwellD (gG B D A H W) (giG B D A H W) (FG Φ Ψ) 0 3 x = ((16:ℝ) * B (x 1) ^ 2 * D (x 1) ^ 2 * A (x 1) * H (x 1) * W (x 1) * x 2 + (-12:ℝ) * B (x 1) ^ 2 * D (x 1) ^ 2 * H (x 1) ^ 2 * W (x 1) * x 2 + (-16:ℝ) * B (x 1) ^ 2 * D (x 1) ^ 2 * H (x 1) * W (x 1) * Ψ (x 1) ^ 2 * x 2 + (2:ℝ) * B (x 1) ^ 2 * D (x 1) * A (x 1) ^ 2 * H (x 1) * deriv (deriv W) (x 1) * x 2 + (3:ℝ) * B (x 1) ^ 2 * D (x 1) * A (x 1) ^ 2 * deriv H (x 1) * deriv W (x 1) * x 2 + (-4:ℝ) * B (x 1) ^ 2 * D (x 1) * A (x 1) ^ 2 * W (x 1) * deriv Ψ (x 1) ^ 2 * x 2 + (-8:ℝ) * B (x 1) ^ 2 * D (x 1) * A (x 1) ^ 2 * deriv Φ (x 1) * deriv Ψ (x 1) * x 2 + (2:ℝ) * B (x 1) ^ 2 * D (x 1) * A (x 1) * deriv A (x 1) * H (x 1) * deriv W (x 1) * x 2 + (-4:ℝ) * B (x 1) ^ 2 * D (x 1) * A (x 1) * deriv (deriv A) (x 1) * H (x 1) * W (x 1) * x 2 + (1:ℝ) * B (x 1) ^ 2 * D (x 1) * deriv A (x 1) ^ 2 * H (x 1) * W (x 1) * x 2 + (-1:ℝ) * B (x 1) ^ 2 * deriv D (x 1) * A (x 1) ^ 2 * H (x 1) * deriv W (x 1) * x 2 + (2:ℝ) * B (x 1) ^ 2 * deriv D (x 1) * A (x 1) * deriv A (x 1) * H (x 1) * W (x 1) * x 2 + (-1:ℝ) * B (x 1) * deriv B (x 1) * D (x 1) * A (x 1) ^ 2 * H (x 1) * deriv W (x 1) * x 2 + (-2:ℝ) * B (x 1) * deriv B (x 1) * D (x 1) * A (x 1) * deriv A (x 1) * H (x 1) * W (x 1) * x 2 + (1:ℝ) * B (x 1) * deriv B (x 1) * deriv D (x 1) * A (x 1) ^ 2 * H (x 1) * W (x 1) * x 2 + (-2:ℝ) * B (x 1) * deriv (deriv B) (x 1) * D (x 1) * A (x 1) ^ 2 * H (x 1) * W (x 1) * x 2 + (3:ℝ) * B (x 1) * D (x 1) * A (x 1) ^ 2 * H (x 1) ^ 2 * W (x 1) * deriv W (x 1) ^ 2 * x 2 + (4:ℝ) * B (x 1) * D (x 1) * A (x 1) ^ 2 * H (x 1) * W (x 1) ^ 3 * deriv Ψ (x 1) ^ 2 * x 2 + (8:ℝ) * B (x 1) * D (x 1) * A (x 1) ^ 2 * H (x 1) * W (x 1) ^ 2 * deriv Φ (x 1) * deriv Ψ (x 1) * x 2 + (4:ℝ) * B (x 1) * D (x 1) * A (x 1) ^ 2 * H (x 1) * W (x 1) * deriv Φ (x 1) ^ 2 * x 2 + (1:ℝ) * deriv B (x 1) ^ 2 * D (x 1) * A (x 1) ^ 2 * H (x 1) * W (x 1) * x 2) / ((4:ℝ) * B (x 1) ^ 2 * D (x 1) ^ 2 * A (x 1) ^ 2) := by sorry
