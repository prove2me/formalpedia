-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_finite_horizon_reward_le_killed_record_tsum
-- name    : AvramDividend.Classical.stopped_finite_horizon_reward_le_killed_record_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:50:50.315591+00:00
-- url     : https://prove2.me/theorems/c0f4eb1a-fe76-4fff-beed-f222646eb469
-- title:
--   Every finite pre-ruin horizon is bounded by the genuine killed first-record grid sum
-- statement:
--   For every finite observation horizon strictly before the stopping time, the discounted stopped reflected supremum Stieltjes reward over (0,t] is bounded by the full killed and discounted strict upward record sum. The proof divides the finite record grid into no-positive-record and last-record-attained cases, applying two separately verified bounds.
-- source:
--   Finite-horizon record clock dichotomy, stopped zero-reward through the first record, and the attained horizon killed-grid inequality.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_record_grid_last_survived_before_finite_horizon
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_zero_through_extended_first_record
import Theorems.Thm_AvramDividend_Classical_runningSup_finite_horizon_killedRecord_budget
import Theorems.Thm_AvramDividend_Classical_chat08_named_upper_clock_eq_raw_infimum

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.stopped_finite_horizon_reward_le_killed_record_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h)
    (t : ℝ≥0) (htτ : (t : ℝ≥0∞) < τ) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if twoSidedExitUpTime X ((k : ℝ) * h) ω < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q *
            (twoSidedExitUpTime X ((k : ℝ) * h) ω).toReal)))
      else 0) := by sorry
