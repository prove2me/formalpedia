-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_residual_future_right_tail
-- name    : AvramDividend.Classical.avram_a06_original_cp_residual_future_right_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:08:46.247195+00:00
-- url     : https://prove2.me/theorems/1eea2cdd-57fe-4e83-9551-ad98d02143ca
-- title:
--   Original rate-one compound-Poisson residual and complete future right-tail rectangles
-- statement:
--   For the original marked compound-Poisson driver, the residual waiting time and the entire future infinite suffix at any nonnegative clock have the same positive-threshold rectangular probabilities as the original first interarrival and its future suffix. This uses the exact original count threshold, iid waits, and a common infinite-product law.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_residual_future_right_tail
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s : ℝ≥0) (t : ℝ) (ht : 0 ≤ t)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    P {ω | t < τ (LevyFoundations.jumpCount
        (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)) ω -
      ((s : ℝ) - ∑ i ∈ Finset.range
        (LevyFoundations.jumpCount
          (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)), τ i ω) ∧
      (fun j : ℕ => τ (LevyFoundations.jumpCount
        (fun i => LevyFoundations.arrival τ i ω) (s : ℝ) + 1 + j) ω) ∈ B} = P {ω | t < τ 0 ω ∧ (fun j : ℕ => τ (1 + j) ω) ∈ B} := by sorry
