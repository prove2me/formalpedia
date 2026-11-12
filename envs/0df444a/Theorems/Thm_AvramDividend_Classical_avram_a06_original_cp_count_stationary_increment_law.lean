-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_stationary_increment_law
-- name    : AvramDividend.Classical.avram_a06_original_cp_count_stationary_increment_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:40:27.549685+00:00
-- url     : https://prove2.me/theorems/d8712078-dbc4-4562-b64e-a264bb6315f6
-- title:
--   Original exponential-renewal jump count has stationary increments in distribution
-- statement:
--   For the original same-space rate-one exponential interarrival compound-Poisson driver, the count increment over any interval of length k has the law of the count increment over the interval from zero to k.
-- source:
--   Prove memorylessness of iid exponential interarrival stream and transfer the original renewal counting process to an original-filtration Poisson count, with zero-clock endpoint treatment. Do not assume the increment law solely from marginal Poisson count laws.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_count_stationary_increment_law
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s k : ℝ≥0) :
    IdentDistrib
      (fun ω => LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ) -
        LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s : ℝ))
      (fun ω => LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (k : ℝ) -
        LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (0 : ℝ)) P P := by sorry
