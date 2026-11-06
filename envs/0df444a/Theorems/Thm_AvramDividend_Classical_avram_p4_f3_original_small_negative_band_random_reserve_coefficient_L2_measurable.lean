-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_small_negative_band_random_reserve_coefficient_L2_measurable
-- name    : AvramDividend.Classical.avram_p4_f3_original_small_negative_band_random_reserve_coefficient_L2_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:03:08.542455+00:00
-- url     : https://prove2.me/theorems/8e862de6-9d0a-4dfd-983f-15243af19d59
-- title:
--   Original negative-band random-reserve squared coefficient intensity is measurable
-- statement:
--   For arbitrary measurable random reserve states, the squared difference of physical jump-value coefficients integrated against the original Levy intensity over a negative small-mark interval is measurable on the original probability space. This is a joint-measurability and product-Lebesgue-integral theorem, independent of stochastic law substitution.
-- source:
--   Uses the Proved original w measurable extension from continuous nonnegative reserve and zero negative payoff, Mathlib product measurability and lintegral_prod_right on original X.ν. Intended to eliminate the explicit inner-integral measurability premise of the random-mesh joint L2 DCT.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative-jump intensity is a measurable function of the random reserve states. -/

theorem AvramDividend.Classical.avram_p4_f3_original_small_negative_band_random_reserve_coefficient_L2_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (U V : Ω → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (ε : ℝ) :
    Measurable (fun ω =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U ω + z) - w (U ω)) -
            (w (V ω + z) - w (V ω))) ^ 2) ∂X.ν)) := by sorry
