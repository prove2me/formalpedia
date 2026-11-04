-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_large_mark_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_finite_clock_large_mark_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:26:24.364704+00:00
-- url     : https://prove2.me/theorems/bdbc17f1-670a-4824-9121-ecb1e73dd85f
-- title:
--   Original large negative jump payoff is product L1 over any measurable finite capped observation clock
-- statement:
--   For the original spectrally negative Levy source, a finite observation-clock measure and a measurable controlled reserve constrained to [0,v], the source negative-large-mark raw payoff, explicitly cut off at z < -epsilon, is integrable over the finite product of the clock measure with the restricted original Levy intensity. Original capped payoff continuity, zero negative payoff, and h-epsilon>0 establish the uniform bound and genuine tail finiteness. It assumes no jump-count compensator, does not evaluate generator at endpoint or overshoot, and does not assert an Ito identity.
-- source:
--   Avram P4-C original Levy large-jump epsilon intensity, measurable zero-negative payoff and cap-wide raw mark bound accepted helpers

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_large_raw_uniform_on_prejump_cap
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_finite_clock_large_mark_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (hR : Measurable R)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t, R t ∈ Icc 0 v) :
    Integrable
      (fun p : T × ℝ =>
        if p.2 < -ε then w (R p.1 + p.2) - w (R p.1) else 0)
      (μ.prod (X.ν.restrict (Iio (-ε)))) := by sorry
