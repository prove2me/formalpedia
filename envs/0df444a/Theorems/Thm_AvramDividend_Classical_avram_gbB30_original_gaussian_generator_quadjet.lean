-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_gaussian_generator_quadjet
-- name    : AvramDividend.Classical.avram_gbB30_original_gaussian_generator_quadjet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T13:25:21.780436+00:00
-- url     : https://prove2.me/theorems/22f5cbee-1b43-44f9-965c-0da868366553
-- title:
--   Original positive-drift unit-Gaussian quadratic generator identity
-- statement:
--   For any original Levy triplet with sigma=1, c=2 and zero jumps, compute the exact generator of a quadratic whose local value and derivatives agree with w(y)=2y-4y². This is an exact original-source generator equality used for the Gaussian cap 1/8 counterexample model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB30_original_gaussian_generator_quadjet
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = (0 : Measure ℝ)) (hσ : X.σ = 1) (hc : X.c = 2)
    (w : ℝ → ℝ) (y : ℝ)
    (hw0 : w y = 2 * y - 4 * y ^ 2)
    (hw1 : deriv w y = 2 - 8 * y)
    (hw2 : iteratedDeriv 2 w y = -8) :
    X.GeneratorIntegrable w y ∧
      X.generator w y - (1 / 100 : ℝ) * w y =
        (1 / 25 : ℝ) * y ^ 2 - (1602 / 100 : ℝ) * y := by sorry
