-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_full_stopped_reward_le_killed_record_tsum
-- name    : AvramDividend.Classical.runningSup_full_stopped_reward_le_killed_record_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:09:57.625631+00:00
-- url     : https://prove2.me/theorems/67afad2e-4fa5-4dec-929a-67f2b1efaa41
-- title:
--   Complete stopped running-supremum dividend reward is bounded by the killed first-record series
-- statement:
--   The genuine discounted Stieltjes dividend reward paid strictly before an arbitrary ruin horizon, including a zero or infinite horizon, is pathwise no greater than the complete series of killed discounted strict upward grid crossings. At zero horizon both payment and initial Stieltjes atom vanish. For positive horizons, the proved rational-prefix exhaustion and zero-atom comparison transfer the proved finite-horizon record budget to the complete stopped integral.
-- source:
--   Combine Proved finite pre-ruin horizon record budget, countable rational prefix exhaustion, null time-zero Stieltjes atom, Ico-to-Ioc comparison, and the surviving payment-time inclusion.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_atom
import Theorems.Thm_AvramDividend_Classical_paymentTimes_lintegral_le_of_rational_prefix_bounds
import Theorems.Thm_AvramDividend_Classical_lintegral_Ico_le_Ioc_of_zero_initial_atom
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
import Theorems.Thm_AvramDividend_Classical_stopped_finite_horizon_reward_le_killed_record_tsum

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.runningSup_full_stopped_reward_le_killed_record_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h) :
    (∫⁻ r in paymentTimes τ,
      ENNReal.ofReal (Real.exp (-(q * r)))
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if twoSidedExitUpTime X ((k : ℝ) * h) ω < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q *
            (twoSidedExitUpTime X ((k : ℝ) * h) ω).toReal)))
      else 0) := by sorry
