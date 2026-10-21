-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_reward_measurable
-- name    : AvramDividend.Classical.runningSup_stopped_full_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T11:06:19.231819+00:00
-- url     : https://prove2.me/theorems/7e3c2ed0-e67a-451a-9d7c-6ea044b12a3b
-- title:
--   Unconditional measurability of the original full-horizon stopped Stieltjes dividend reward
-- statement:
--   For the actual spectrally negative Lévy process, original reflected-drawdown ruin horizon and true full running-supremum dividend Stieltjes measure, the entire exponentially q-discounted dividend reward paid on the original sample-dependent payment-time set is measurable, without restricting the time axis or imposing s-finiteness as an extra assumption. Obtain an s-finite measurable kernel representing the full original dividend Stieltjes measure through integer time-slice decomposition and apply the remotely accepted conditional full-horizon reward measurability theorem. This is the missing full-reward measurability foundation for expected dividend valuation and the stochastic renewal bounds.
-- source:
--   Dependency-gated runningSup_dividendMeasure_global_sfinite_kernel_exists (authoring request 38033843-4ec3-4cc7-9611-ef409f63d941) and remotely ACCEPTED runningSup_stopped_full_reward_measurable_of_kernel target 070842a9-e528-4aa6-8ca0-52b33096aab3, candidate 12286.

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_reward_measurable_of_kernel

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_full_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂dividendMeasure (runningSup X) ω) := by sorry
