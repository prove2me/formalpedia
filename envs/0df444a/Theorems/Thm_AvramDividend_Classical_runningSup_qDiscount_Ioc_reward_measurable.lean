-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_Ioc_reward_measurable
-- name    : AvramDividend.Classical.runningSup_qDiscount_Ioc_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:19:07.110175+00:00
-- url     : https://prove2.me/theorems/653bdc1c-7420-4a08-8889-45e9fab661f7
-- title:
--   Fixed-interval q-discounted running-supremum Stieltjes reward is a measurable random variable
-- statement:
--   For the actual running-supremum dividend Stieltjes measure of a spectrally negative Lévy process, the exponentially q-discounted integral over any fixed half-open real-time interval is measurable as a function of the sample point. Use the previously established measurable random interval-restricted Stieltjes measure, the continuous exponential and ENNReal.ofReal embedding, and the pinned Mathlib Giry-monad theorem that integrating a deterministic nonnegative measurable function against a measurable measure-valued map produces a measurable random variable. This handles unrestricted interval payouts, providing one substantive ingredient towards a.e. measurability of the corresponding *stopped* interval rewards and the unconditional expectation/countable-sum interchange.
-- source:
--   Dependency-gated runningSup_dividendMeasure_restrict_Ioc_measurable; pinned MeasureTheory.Measure.measurable_lintegral (private signature probe job 9aa0cbd6-5135-4ef7-9c08-d55add092ab6), Real.measurable_exp and ENNReal.measurable_ofReal.

import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_qDiscount_Ioc_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q l u : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ r in Set.Ioc l u,
        ENNReal.ofReal (Real.exp (-(q * r)))
        ∂(dividendMeasure (runningSup X) ω)) := by sorry
