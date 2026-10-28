-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_exp_clock_small_rate_bounded_horizon_mass
-- name    : AvramDividend.Classical.esscher_exp_clock_small_rate_bounded_horizon_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:38:19.581171+00:00
-- url     : https://prove2.me/theorems/64467ba3-57d2-4332-9bdb-fce5677294ed
-- title:
--   Vanishing-rate genuine exponential clocks escape every fixed bounded time horizon
-- statement:
--   For any strictly positive sequence of actual exponential clock rates p_n tending to zero and any fixed nonnegative time T, the true exponential probability expMeasure(p_n)(Iic T) tends to zero in ENNReal. This proves the early-clock mass vanishes, rather than assuming a clock-distribution scaling identity; it is the crucial independent probabilistic concentration bound for the finite-to-perpetual Esscher survival-CDF limit.
-- source:
--   Pinned Mathlib ProbabilityTheory.cdf_expMeasure_eq, ProbabilityTheory.ofReal_cdf, ENNReal.continuous_ofReal and continuous real exp, revision 0df444a. Neither a Wiener-Hopf factor nor a tilted infinite-horizon path law is used.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

open ProbabilityTheory MeasureTheory Filter Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_exp_clock_small_rate_bounded_horizon_mass
    (p : ℕ → ℝ) (hp : Tendsto p atTop (nhds (0 : ℝ)))
    (hpos : ∀ n, 0 < p n)
    (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n => expMeasure (p n) (Iic T))
      atTop (nhds (0 : ℝ≥0∞)) := by sorry
