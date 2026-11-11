-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_raw_isLevyProcess
-- name    : AvramDividend.Classical.avram_a06_original_cp_raw_isLevyProcess
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T20:22:10.548615+00:00
-- url     : https://prove2.me/theorems/7afcd2ae-27c7-4a2c-8839-1a84bbee6a3f
-- title:
--   Original canonical compound-Poisson path is a Lévy process under the original driver
-- statement:
--   Prove stationary independent increments, stochastic continuity and zero start for the original uniform-mark compound Poisson path using the original independent interarrival and mark driver. No auxiliary process or cross-space equality.
-- source:
--   Genuine stochastic-increment prerequisite for path-increment certificate d4e19a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_raw_isLevyProcess
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    IsLevyProcess
      (fun t : ℝ≥0 => LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ)) P := by sorry
