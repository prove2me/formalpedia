-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_stopped_Ioc_reward_measurable_of_sfinite
-- name    : AvramDividend.Classical.runningSup_qDiscount_stopped_Ioc_reward_measurable_of_sfinite
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T08:19:05.090994+00:00
-- url     : https://prove2.me/theorems/a36b05af-267a-443c-bb73-1db6bcff6d21
-- title:
--   Original stopped interval q-discounted Stieltjes reward measurable under explicit s-finite random kernel
-- statement:
--   The actual running-supremum dividend Stieltjes reward paid on a fixed half-open real-time interval before the original reflected ruin time is a measurable sample-path random variable, provided the interval-restricted random Stieltjes kernel is s-finite. The proof invokes the published jointly measurable original barrier-payment set, the measurable interval-restricted actual dividend kernel, and the general jointly measurable nonnegative s-finite kernel integral theorem. Its single s-finiteness condition is explicit and must be discharged separately before unconditional expected reward summation can be claimed.
-- source:
--   Dependency-gated barrierPaymentRegion_measurable authoring request e9396bef-4ce8-4f60-aeec-d7e284a3e16a and measurable_random_indicator_lintegral target 3f6e3e3b-9b82-4ca2-9ad8-b0543533321f. Proved runningSup_dividendMeasure_restrict_Ioc_measurable target d763694e-e35d-43bf-90d6-3d1a42a067ed.

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable
import Theorems.Thm_AvramDividend_Classical_barrierPaymentRegion_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_qDiscount_stopped_Ioc_reward_measurable_of_sfinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q l u : ℝ)
    [ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.mk
      (fun ω : Ω =>
        (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u))
      (runningSup_dividendMeasure_restrict_Ioc_measurable X l u))] :
    Measurable (fun ω : Ω =>
      ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) := by sorry
