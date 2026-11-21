-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_infiniteactivity_full_negative_generator_lower_from_smallcomp
-- name    : AvramDividend.Classical.avram_f6_original_infiniteactivity_full_negative_generator_lower_from_smallcomp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:30:31.089187+00:00
-- url     : https://prove2.me/theorems/dd598d3b-bd31-4004-84f8-30eaa71c4e92
-- title:
--   Actual infinite-activity Lévy full negative generator integral bounded below by small-compensator minus finite large rate
-- statement:
--   For arbitrary original spectrally negative Lévy X including infinite negative jump activity, true GeneratorIntegrable w y, w≥0 and w′(y)≥0, the original full ν integral generator is ≥ genuine small compensated ν(-1,0) integral minus the finite rate ν((−∞,−1]) times w(y). This combines the true unit-boundary generator integral split and large-mark integrable lower bound and keeps the small compensation explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_infiniteactivity_full_negative_generator_lower_from_smallcomp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (y : ℝ)
    (hwpos : ∀ u : ℝ, 0 ≤ w u)
    (hderiv : 0 ≤ deriv w y)
    (hGen : X.GeneratorIntegrable w y) :
    (∫ z in Ioo (-1 : ℝ) 0,
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) -
      (X.ν (Iic (-1 : ℝ))).toReal * w y ≤
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by sorry
