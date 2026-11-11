-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_driver_exists
-- name    : AvramDividend.Classical.avram_a06_uniform_negative_mark_driver_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T16:25:36.066605+00:00
-- url     : https://prove2.me/theorems/726c336d-0600-4318-8d55-32c0398638a5
-- title:
--   Independent compound-Poisson driver with diffuse negative unit-interval marks
-- statement:
--   Construct independent exponential waiting times with positive unit rate and iid continuously distributed strictly negative jump marks uniformly distributed on (-1,0). The mark law is a probability measure because that interval has length one, and the accepted compound-Poisson driver existence theorem gives an original abstract probability space with jointly independent streams. This is an explicit stochastic input for the A06 bounded-variation source witness.
-- source:
--   Root-related child of the Open A06 source construction 115c3b1e. Reuses Proved public levy_foundations_compoundPoissonDriverExists f9e2e0b5. Does not by itself construct a filtered Avram SpectrallyNegativeLevy process; that adapter remains a separate obligation.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_levy_foundations_compoundPoissonDriverExists

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_uniform_negative_mark_driver_exists :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (τ Y : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧
      LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P := by sorry
