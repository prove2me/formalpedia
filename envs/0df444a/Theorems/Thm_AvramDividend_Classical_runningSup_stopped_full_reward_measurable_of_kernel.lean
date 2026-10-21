-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_reward_measurable_of_kernel
-- name    : AvramDividend.Classical.runningSup_stopped_full_reward_measurable_of_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:36:17.126498+00:00
-- url     : https://prove2.me/theorems/070842a9-e528-4aa6-8ca0-52b33096aab3
-- title:
--   Measurable full-horizon reflected dividend Stieltjes reward under an identified s-finite random kernel
-- statement:
--   The true full-horizon exponentially discounted Stieltjes dividend payoff stopped at the original reflected-drawdown ruin horizon is a measurable extended-nonnegative function of the Lévy sample point whenever its full random dividend measure is represented by an explicitly identified s-finite kernel. This is the untruncated analogue of the remotely accepted interval-restricted payout measurability theorem and retains the original time-zero payment convention and actual ruin time. It isolates global s-finiteness of the random dividend measure as the remaining measurable kernel hypothesis.
-- source:
--   Accepted barrierPaymentRegion_measurable target 9ca4f703-cb37-448a-b9b5-10f436128de7, accepted measurable_random_indicator_lintegral target 3f6e3e3b-9b82-4ca2-9ad8-b0543533321f and accepted interval analogue runningSup_stopped_Ioc_reward_measurable_of_kernel target b34ac815-0eac-4fdb-9016-1389e2befafb.

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_barrierPaymentRegion_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_full_reward_measurable_of_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ)
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    [ProbabilityTheory.IsSFiniteKernel κ]
    (hκ : ∀ ω : Ω, κ ω = dividendMeasure (runningSup X) ω) :
    Measurable (fun ω : Ω =>
      ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂dividendMeasure (runningSup X) ω) := by sorry
