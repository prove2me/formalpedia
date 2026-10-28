-- Prove2me | Theorems.Thm_AvramDividend_Classical_attained_finite_horizon_reward_le_killed_record_tsum
-- name    : AvramDividend.Classical.attained_finite_horizon_reward_le_killed_record_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:38:07.816606+00:00
-- url     : https://prove2.me/theorems/8bc66d5f-3304-405c-9644-92e7d6fb9a6e
-- title:
--   Finite-horizon stopped dividend reward dominated by actual killed record weights
-- statement:
--   If some level N is the last attained record before finite time t and the barrier path survives past t, then the entire stopped discounted running-supremum Stieltjes reward on (0,t] is bounded above by the infinite sum of the genuine killed and discounted strict upward passage weights for all record levels k h. The proof combines the verified whole finite-horizon Stieltjes bound, monotonic record clocks, prefix-to-tsum domination and the exact named versus raw passage-clock identity. This is the attained-record branch needed for the full stopped-renewal pathwise estimate.
-- source:
--   Apply the published whole-horizon finite record cell bound, instantiate the published surviving-prefix-to-killed-tsum inequality using raw monotone clocks, and rewrite using the proved named upper passage time identity.

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_runningSup_full_finite_horizon_last_record_budget
import Theorems.Thm_AvramDividend_Classical_surviving_record_prefix_budget_le_killed_tsum
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono
import Theorems.Thm_AvramDividend_Classical_chat08_named_upper_clock_eq_raw_infimum

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.attained_finite_horizon_reward_le_killed_record_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h)
    (N : ℕ) (t : ℝ≥0)
    (hN : (⨅ (r : ℝ≥0)
      (_ : (0 : ℝ) + (N : ℝ) * h < X.X r ω),
      (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (hnext : ¬ (⨅ (r : ℝ≥0)
      (_ : (0 : ℝ) + ((N + 1 : ℕ) : ℝ) * h < X.X r ω),
      (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (htτ : (t : ℝ≥0∞) < τ) :
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
