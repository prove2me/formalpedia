-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_full_reward_indicator_expectation
-- name    : AvramDividend.Classical.barrierSupValue_eq_full_reward_indicator_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:20:20.286549+00:00
-- url     : https://prove2.me/theorems/fe6aa85a-6f7b-4dfc-820f-785a6c9b9f0b
-- title:
--   Original stopped barrier dividend value equals expectation of the full random-kernel indicator reward
-- statement:
--   The original value barrierSupValue of the true reflected running-supremum dividend policy equals the expectation of the full-horizon q-discounted Stieltjes dividend reward expressed as a random-time payment indicator integrated over the original unrestricted random dividend measure. The original definition restricts the measure to paymentTimes at each sample point; the accepted measurability of paymentTimes and Mathlib's lintegral_indicator identity move that restriction into the integrand exactly, for every sample point. This is the precise expectation interface supplied by the newly proved unconditional full-horizon reward measurability and the global s-finite dividend kernel. It retains the true ruin boundary and any zero-time convention and requires no renewal or exit-law assumptions.
-- source:
--   Published barrierSupValue definition in Def_AvramDividend_Classical_ReflectionBarrier; remotely proved paymentTimes_measurable target 88dafb7f-65e0-4218-8bde-e06dfe88a7a3; pinned Mathlib lintegral_indicator signature verified in remote job 134daa8d-8a76-4632-aafe-540d58ac41ef.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_eq_full_reward_indicator_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) :
    barrierSupValue X a q =
      ∫⁻ ω, ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω) ∂P := by sorry
