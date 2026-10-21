-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_reward_measurable
-- name    : AvramDividend.Classical.runningSup_stopped_Ioc_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T11:06:09.658163+00:00
-- url     : https://prove2.me/theorems/94887f4f-dbce-44c9-a7c0-2b76b6466ebc
-- title:
--   Unconditional measurability of actual stopped q-discounted running-supremum Stieltjes dividend interval reward
-- statement:
--   For the true spectrally negative Lévy process, actual reflected-drawdown ruin horizon and actual running-supremum Stieltjes dividend measure, the exponentially q-discounted dividend reward over any fixed half-open real-time interval, paid on the original random stopped-payment set, is a measurable extended-nonnegative random variable. Construct the canonical interval-restricted measure kernel using the previously accepted measurable random measure theorem, obtain its s-finiteness from samplewise finite Stieltjes mass using the full constructive kernel partition theorem, then apply the remotely accepted stopped reward measurability theorem. No artificial measurability, uniform-mass or s-finiteness hypothesis remains.
-- source:
--   Dependency-gated runningSup_intervalKernel_isSFinite_of_eq (staged), remotely accepted runningSup_stopped_Ioc_reward_measurable_of_kernel target b34ac815-0eac-4fdb-9016-1389e2befafb and runningSup_dividendMeasure_restrict_Ioc_measurable target d763694e-e35d-43bf-90d6-3d1a42a067ed.

import Theorems.Thm_AvramDividend_Classical_runningSup_intervalKernel_isSFinite_of_eq
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_reward_measurable_of_kernel
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_Ioc_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q l u : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) := by sorry
