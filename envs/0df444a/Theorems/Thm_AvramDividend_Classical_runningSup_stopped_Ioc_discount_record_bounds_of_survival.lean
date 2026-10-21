-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_discount_record_bounds_of_survival
-- name    : AvramDividend.Classical.runningSup_stopped_Ioc_discount_record_bounds_of_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T16:33:48.94354+00:00
-- url     : https://prove2.me/theorems/7d59aefb-31f3-40d2-85e0-b0477c351129
-- title:
--   Stopped discounted Stieltjes record-increment bounds on an interval entirely surviving before ruin
-- statement:
--   Let the actual stopped payment-time set of a spectrally negative Lévy running-supremum regulator contain an entire fixed half-open interval (s,t]. For any nonnegative discount rate, the true stopped Stieltjes dividends paid on that interval are bounded below by the terminal q-discount factor times the actual running-record increment and above by the initial q-discount factor times the same increment. This is a genuine two-sided bound for the original stopped payout on fully survived time intervals, using no Markov or two-sided exit assumptions. It combines the accepted original interval Stieltjes endpoint bounds with the exact restriction-of-measure identity showing stopping is immaterial on an interval wholly contained in the original payment set.
-- source:
--   Accepted runningSup_qDiscount_interval_record_bounds target ab0e5769-ea91-4590-86ca-a4d137108409; accepted paymentTimes_measurable target 88dafb7f-65e0-4218-8bde-e06dfe88a7a3; staged generic interval restriction-of-subset helper request 1d6f73a0-c140-4af4-9ae7-5db9f296a86f.

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_lintegral_indicator_restrict_of_subset
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_interval_record_bounds

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_Ioc_discount_record_bounds_of_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) (s t : ℝ)
    (hSurvive : Set.Ioc s t ⊆ paymentTimes τ) :
    (ENNReal.ofReal (Real.exp (-(q * t))) *
        ENNReal.ofReal
          (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) ≤
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ∧
    ((∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * s))) *
        ENNReal.ofReal
          (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω)) := by sorry
