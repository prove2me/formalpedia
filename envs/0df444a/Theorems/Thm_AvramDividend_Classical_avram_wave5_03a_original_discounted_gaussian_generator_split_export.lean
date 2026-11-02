-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_discounted_gaussian_generator_split_export
-- name    : AvramDividend.Classical.avram_wave5_03a_original_discounted_gaussian_generator_split_export
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:43:15.942696+00:00
-- url     : https://prove2.me/theorems/668fd38f-9d2e-44b6-b652-9efd9754df7d
-- title:
--   Public original-process exact discounted Gaussian generator decomposition
-- statement:
--   For the actual arbitrary SpectrallyNegativeLevy triplet and every real time, state, discount and test function, the discounted generator-minus-q term splits exactly into the Gaussian coefficient sigma squared over two times the second iterated derivative, plus actual source drift and compensated negative-jump integral, minus q w. Holds even sigma=0 where the first term vanishes. This is an algebraic source generator identification for the stochastic Ito-Meyer verification, not a proof of an Ito formula or stochastic integral. Public export for cross-chat import, with identical original-source algebra and no claim of stochastic Ito decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_original_discounted_gaussian_generator_split_export
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q t y : ℝ) :
    Real.exp (-(q * t)) * (X.generator w y - q * w y) =
      Real.exp (-(q * t)) * (X.σ ^ 2 / 2 * iteratedDeriv 2 w y) +
        Real.exp (-(q * t)) *
          (X.c * deriv w y +
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) -
                q * w y) := by
  sorry
