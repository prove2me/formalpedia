-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_raw_stationary_increments
-- name    : AvramDividend.Classical.avram_a06_original_compound_raw_stationary_increments
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T00:08:06.732655+00:00
-- url     : https://prove2.me/theorems/c73e7059-cb18-4a60-93bf-17adb61f45ca
-- title:
--   Original compound-Poisson marked renewal process has stationary increments
-- statement:
--   Exponential memorylessness and identically distributed marks imply stationary increments on the original product probability space.
-- source:
--   A06 original marked-compound-Poisson renewal driver with exact rate and diffuse negative marks, root-connected via accepted gated Lévy reduction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_compound_raw_stationary_increments
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    HasStationaryIncrements
      (fun (t : ℝ≥0) ω => LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω) P := by sorry
