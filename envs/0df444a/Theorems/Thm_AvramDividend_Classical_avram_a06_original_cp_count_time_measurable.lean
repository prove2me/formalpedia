-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_time_measurable
-- name    : AvramDividend.Classical.avram_a06_original_cp_count_time_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:17:54.620642+00:00
-- url     : https://prove2.me/theorems/37a2d96f-9b52-42ba-8b63-d6a5601f2bf3
-- title:
--   Original compound Poisson count at every fixed real time is measurable
-- statement:
--   For an original rate-one compound Poisson driver, the renewal count at any deterministic real horizon is measurable as a random variable. This promotes a proved private helper out of the existing finite-grid count-increment measurability proof and is needed to apply the countwise almost-sure independence theorem.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_count_time_measurable
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (t : ℝ) :
    Measurable (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) t) := by sorry
