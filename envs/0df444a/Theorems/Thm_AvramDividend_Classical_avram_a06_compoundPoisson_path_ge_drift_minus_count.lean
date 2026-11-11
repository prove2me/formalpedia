-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_path_ge_drift_minus_count
-- name    : AvramDividend.Classical.avram_a06_compoundPoisson_path_ge_drift_minus_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:13:03.429248+00:00
-- url     : https://prove2.me/theorems/bf877ffb-df80-4460-9a85-42b9d2d9c497
-- title:
--   Compound-Poisson negative jump path bounded below by drift minus jump count
-- statement:
--   If every mark lies above −1, its finite-sum jump contribution is at least minus the number of jumps. The original compound-Poisson path is consequently between drift minus jump count and drift.
-- source:
--   Original first-moment field of fd251b85 and public bounded negative marks; source exact definitional jumpCount and piecewisePath.

import Mathlib
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_piecewisePath
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_compoundPoisson_path_ge_drift_minus_count
    {Ω : Type*} (b : ℝ) (τ Y : ℕ → Ω → ℝ) (ω : Ω)
    (hmarks : ∀ n, -1 ≤ Y n ω) (t : ℝ) :
    b * t - (LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) t : ℝ) ≤
      LevyFoundations.compoundPoisson b τ Y t ω := by sorry
