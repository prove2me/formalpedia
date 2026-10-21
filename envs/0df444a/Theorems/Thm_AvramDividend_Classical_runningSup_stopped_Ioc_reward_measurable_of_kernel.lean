-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_reward_measurable_of_kernel
-- name    : AvramDividend.Classical.runningSup_stopped_Ioc_reward_measurable_of_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:24:39.87536+00:00
-- url     : https://prove2.me/theorems/b34ac815-0eac-4fdb-9016-1389e2befafb
-- title:
--   Stopped Stieltjes dividend interval reward measurable when the actual random measure has an s-finite kernel representation
-- statement:
--   For the original reflected-barrier stopping time and the true running-supremum dividend Stieltjes measure, the exponentially discounted stopped dividend reward restricted to an arbitrary fixed half-open real-time interval is a measurable ENNReal random variable, whenever an explicitly given s-finite kernel equals the original interval-restricted sample-path measure. The equality condition and s-finiteness instance remain explicit; this is the downstream theorem enabled by constructing a genuine samplewise-finite random-measure kernel and proving its s-finiteness.
-- source:
--   Accepted barrierPaymentRegion_measurable target 9ca4f703-cb37-448a-b9b5-10f436128de7 and measurable_random_indicator_lintegral target 3f6e3e3b-9b82-4ca2-9ad8-b0543533321f. This version parameterises the kernel to keep the canonical target parser independent from an imported helper theorem within an instance binder.

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_barrierPaymentRegion_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_Ioc_reward_measurable_of_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q l u : ℝ)
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    [ProbabilityTheory.IsSFiniteKernel κ]
    (hκ : ∀ ω : Ω, κ ω =
      (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) :
    Measurable (fun ω : Ω =>
      ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) := by sorry
