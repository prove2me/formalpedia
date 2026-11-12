-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_threshold_ae
-- name    : AvramDividend.Classical.avram_a06_original_cp_count_threshold_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:13:12.473394+00:00
-- url     : https://prove2.me/theorems/d5a32c5b-7bb1-46ef-8869-e99ff33ee348
-- title:
--   Original compound-Poisson completed-arrival count has the exact renewal prefix threshold almost surely
-- statement:
--   For the original exponential-interarrival compound-Poisson driver, the number of arrivals by every real time exceeds n precisely when the first n+1 interarrival times sum to at most that time, simultaneously for all horizons and indices outside one null set.
-- source:
--   Combine proved levy_foundations_compoundDriverArrivalStrictMono and levy_foundations_compoundDriverArrivalDiverges with proved levy_foundations_jumpCountLtIff, then unfold the original arrival partial sum.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_count_threshold_ae
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, ∀ (u : ℝ) (n : ℕ),
      n < LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) u ↔
        (∑ i ∈ Finset.range (n + 1), τ i ω) ≤ u := by sorry
