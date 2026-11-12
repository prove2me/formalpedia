-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_driver_interarrival_independent
-- name    : AvramDividend.Classical.avram_a06_original_compound_driver_interarrival_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:13:48.543598+00:00
-- url     : https://prove2.me/theorems/cffcbe66-3e19-4f5c-9d46-4b5ddb4520ee
-- title:
--   Original compound Poisson driver's interarrivals are independent
-- statement:
--   The driver hypothesis asserts joint independence of the interarrival and mark families indexed by a sum type. Restricting to the injectively indexed interarrival coordinates gives their independent family on the original probability space.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_compound_driver_interarrival_independent
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    iIndepFun τ P := by sorry
