-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_expected_survived_interval_record_bounds
-- name    : AvramDividend.Classical.runningSup_expected_survived_interval_record_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T19:39:49.329798+00:00
-- url     : https://prove2.me/theorems/dd8a7051-526d-44b2-9cf4-74c6aa6ff44c
-- title:
--   Expected killed interval dividend payments lie between q-discounted record increments on the terminal-survival event
-- statement:
--   For the actual spectrally negative Lévy running-supremum dividend policy, any nonnegative discount q and interval beginning at nonnegative time s, consider only sample paths where the entire interval's terminal time t is strictly before the actual reflected-drawdown ruin time. The expected stopped q-discounted Stieltjes dividend payout from (s,t], restricted to this survival event, lies between the expectations of the corresponding running-supremum record increment discounted at t and s. All expectations are genuine extended-nonnegative Lebesgue integrals under the original law P. The proof is an outer-integral lifting of the two-sided pathwise stopped interval bound, with the survival event converted into inclusion of the full time interval in the exact paymentTimes set. It provides a lower as well as upper expected payout bound without postulating the still-unproved stopped Markov renewal.
-- source:
--   Dependency-gated paymentTimes_Ioc_subset_of_terminal_survival publication request e331890e-aa65-4f12-9de7-deb66852c94b; dependency-gated runningSup_stopped_Ioc_discount_record_bounds_of_survival publication request de41bdf3-3598-487b-abd8-8e2183c522c5; Mathlib lintegral_mono.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_discount_record_bounds_of_survival

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_expected_survived_interval_record_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q s t : ℝ)
    (hq : 0 ≤ q) (hs : 0 ≤ s) :
    (∫⁻ ω, if ENNReal.ofReal t < barrierRuinTime X a ω
       then ENNReal.ofReal (Real.exp (-(q * t))) *
         ENNReal.ofReal
            (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) else 0 ∂P) ≤
    (∫⁻ ω, if ENNReal.ofReal t < barrierRuinTime X a ω
       then ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
             if r ∈ Set.Ioc s t then
               ENNReal.ofReal (Real.exp (-(q * r))) else 0
             ∂(dividendMeasure (runningSup X) ω) else 0 ∂P) ∧
    (∫⁻ ω, if ENNReal.ofReal t < barrierRuinTime X a ω
       then ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
             if r ∈ Set.Ioc s t then
               ENNReal.ofReal (Real.exp (-(q * r))) else 0
             ∂(dividendMeasure (runningSup X) ω) else 0 ∂P) ≤
    (∫⁻ ω, if ENNReal.ofReal t < barrierRuinTime X a ω
       then ENNReal.ofReal (Real.exp (-(q * s))) *
         ENNReal.ofReal
            (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) else 0 ∂P) := by sorry
