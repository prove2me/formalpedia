-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_compoundPoisson_compensated_exponent
-- name    : AvramDividend.Classical.avram_a06_uniform_compoundPoisson_compensated_exponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:49:08.588207+00:00
-- url     : https://prove2.me/theorems/fa25b11f-d8ec-4cb8-9f2f-c9e5ef5bb2b2
-- title:
--   Compensated Lévy exponent simplifies to the compact negative-mark exponent
-- statement:
--   The truncation compensator cancels against the drift coefficient 1 plus the first moment of the uniform negative mark measure.
-- source:
--   A06 original Laplace identity; purely deterministic compensated-generator calculation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_uniform_compoundPoisson_compensated_exponent
    (θ : ℝ) (hθ : 0 ≤ θ) :
    θ + (∫ y in Ioo (-1 : ℝ) 0,
      (Real.exp (θ * y) - 1) ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) =
      laplaceExponent
        ((1 : ℝ) + (∫ y in Ioo (-1 : ℝ) 0,
          y ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))))
        0 ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) θ := by sorry
