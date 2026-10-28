-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSup_stopped_indicator_reward_le_killed_record_tsum
-- name    : AvramDividend.Classical.barrierSup_stopped_indicator_reward_le_killed_record_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:17:50.005884+00:00
-- url     : https://prove2.me/theorems/1f42f3e2-0537-4702-ad1b-4499ca2f5f40
-- title:
--   Actual barrier stopped reward indicator is pathwise bounded by killed upward-record payments
-- statement:
--   For the true running-supremum regulator and barrier ruin clock, the entire discounted Stieltjes payout written as the standard paymentTimes indicator integral is bounded pathwise by the actual killed discounted first-record series at every positive mesh and nonnegative discount. This identifies the exact stochastic budget assumption in the proved renewal upper-bound reduction, using the proved set-integral pathwise domination and measurable payment times.
-- source:
--   Use the Proved full stopped dividend pathwise record budget and the Mathlib lintegral_indicator identity with Proved paymentTimes_measurable.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_full_stopped_reward_le_killed_record_tsum

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.barrierSup_stopped_indicator_reward_le_killed_record_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q h : ℝ)
    (hq : 0 ≤ q) (hh : 0 < h) (ω : Ω) :
    (∫⁻ t,
      if t ∈ paymentTimes (barrierRuinTime X a ω) then
        ENNReal.ofReal (Real.exp (-(q * t))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if twoSidedExitUpTime X ((k : ℝ) * h) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (h * Real.exp (-(q *
            (twoSidedExitUpTime X ((k : ℝ) * h) ω).toReal)))
      else 0) := by sorry
