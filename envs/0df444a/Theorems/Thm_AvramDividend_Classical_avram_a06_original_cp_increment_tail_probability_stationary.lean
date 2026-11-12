-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_increment_tail_probability_stationary
-- name    : AvramDividend.Classical.avram_a06_original_cp_increment_tail_probability_stationary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:48:54.207534+00:00
-- url     : https://prove2.me/theorems/e3d8e9c1-6f68-4ad4-8237-0aaf2a6be1b9
-- title:
--   Original compound-Poisson count-increment strict tail probabilities are stationary
-- statement:
--   For the original marked compound-Poisson driver, the probability of more than m arrivals in a forward interval of length k equals that in the interval from time zero. The proof transports a finite prefix event through the proved entire residual waiting-time stream law; it does not postulate a Poisson process on another space.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_increment_tail_probability_stationary
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s k : ℝ≥0) (m : ℕ) :
    P {ω | m < LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ) -
      LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (s : ℝ)} =
    P {ω | m < LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (k : ℝ) -
      LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (0 : ℝ)} := by sorry
