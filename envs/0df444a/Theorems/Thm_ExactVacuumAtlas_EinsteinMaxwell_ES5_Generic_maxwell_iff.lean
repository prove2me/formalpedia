-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_Generic_maxwell_iff
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.maxwell_iff
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-28T14:06:55.357434+00:00
-- url     : https://prove2.me/theorems/c79ed2e1-c98e-4fe4-b16d-dc5a12233787
-- title:
--   Reduced Maxwell equations: five components ⇔ two radial equations
-- statement:
--   Reduced Maxwell equations: five components ⇔ two radial equations
--
--   Under ESData R B D A H W Φ Ψ, for x ∈ esDomain R: (∀ b, maxwellDiv (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) b x = 0) ⇔ redJ_t = 0 ∧ redJ_σ = 0 at r = x 1.
--
--   **Scope.** All radial data (B, D, A, H, W, Φ, Ψ : ℝ → ℝ) and every R : Set ℝ with ESData R B D A H W Φ Ψ (R open, the seven functions C^∞ on R, B, D, A, H ≠ 0 on R); domain esDomain R = {x | x 1 ∈ R ∧ 0 < x 2 ∧ x 2 < 1}.
--
--   **中文摘要** ESData 下：5 个 Maxwell 散度分量为零 ⇔ 两个约化 Maxwell 方程 redJ_t、redJ_σ 在 r = x 1 处为零。
-- source:
--   He Wang, Exact Spacetime Atlas VI: Five-Dimensional Einstein–Maxwell Certificates and Equal-Spin Radial Reduction. Local source, no public repository; commit 4a4048a; Atlas/EinsteinMaxwell/ES5/Generic/Reduced.lean#L512-L521; SHA-256 9b826fa37b3eb742414809da83be125f760708c6b7efb905716682ad3dda2820. Registered definitions: mission/PHYSICS_BOUNDARY.md (§N–§O); literature: R. C. Myers, M. J. Perry, Ann. Phys. 172 (1986) 304; F. R. Tangherlini, Nuovo Cimento 27 (1963) 636.

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.Generic.maxwell_iff (hE : ESData R B D A H W Φ Ψ) (x : Pt 5) (hx : x ∈ (esDomain R)) :
    (∀ b, maxwellDiv (esMetric B D A H W) (esInverse B D A H W) (esFaraday Φ Ψ) b x = 0) ↔ redJ_t B D A H W Φ Ψ (x 1) = 0 ∧ redJ_σ B D A H W Φ Ψ (x 1) = 0 := by sorry
