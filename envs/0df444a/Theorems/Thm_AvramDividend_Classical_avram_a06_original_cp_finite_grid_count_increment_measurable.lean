-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_finite_grid_count_increment_measurable
-- name    : AvramDividend.Classical.avram_a06_original_cp_finite_grid_count_increment_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:40:48.1732+00:00
-- url     : https://prove2.me/theorems/24563b34-a7a0-4ff0-b2e4-690d063f24ee
-- title:
--   Original compound-Poisson count differences are measurable on any finite deterministic grid
-- statement:
--   Under the exact original compound Poisson driver, each count by a deterministic time is measurable, so the difference of counts on any ordered finite grid is measurable. Extract the measurable interarrival field from IsCompoundPoissonDriver and apply the already-Proved compoundPoissonRandomJumpCountMeasurable theorem to both endpoints.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_finite_grid_count_increment_measurable
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      ∀ i : Fin n, Measurable (fun ω =>
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ)) := by sorry
