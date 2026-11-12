-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_residual_future_measurable
-- name    : AvramDividend.Classical.avram_a06_original_cp_residual_future_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:24:52.621083+00:00
-- url     : https://prove2.me/theorems/33dc39c6-1738-4185-a630-ad800cdd3d99
-- title:
--   Original compound-Poisson residual and complete future suffix measurable
-- statement:
--   Under the original marked renewal driver assumptions, the random-indexed interarrival, its completed finite prefix, and the complete future waiting-time suffix are jointly measurable on the original sample space. This supplies the AEMeasurable premise for positive-tail rectangle law identification.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_residual_future_measurable
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s : ℝ≥0) :
    Measurable (fun ω => (τ (LevyFoundations.jumpCount
        (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)) ω -
      ((s : ℝ) - ∑ i ∈ Finset.range
        (LevyFoundations.jumpCount
          (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)), τ i ω),
      fun j : ℕ => τ (LevyFoundations.jumpCount
        (fun i => LevyFoundations.arrival τ i ω) (s : ℝ) + 1 + j) ω)) := by sorry
