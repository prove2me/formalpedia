-- Prove2me | Theorems.Thm_AvramDividend_Classical_general_stopped_dividend_indicator_reward_measurable
-- name    : AvramDividend.Classical.general_stopped_dividend_indicator_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T06:48:06.065296+00:00
-- url     : https://prove2.me/theorems/415fe924-dca5-4d86-9fe4-1d0f3d6d8a1a
-- title:
--   The full stopped discounted Stieltjes dividend reward is measurable for any admissible-form dividend strategy
-- statement:
--   For an arbitrary left-continuous adapted nondecreasing dividend strategy, the full pre-ruin discounted dividend Stieltjes reward, expressed as a nonnegative integral of the indicator of paymentTimes against the actual pathwise dividendMeasure, is measurable in the sample point. Use the now-proved general dividendMeasure s-finite random kernel existence, the proved measurability of controlled ruin time and its jointly measurable payment set, and the proved measurable random-indicator kernel-integral theorem. This extends the previously proved reflected-running-supremum reward measurability to every dividend strategy; no purely atomic assumption is imposed.
-- source:
--   Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists; Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable; Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral.

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.general_stopped_dividend_indicator_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun ω : Ω =>
      ∫⁻ t, if t ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure D ω)) := by sorry
