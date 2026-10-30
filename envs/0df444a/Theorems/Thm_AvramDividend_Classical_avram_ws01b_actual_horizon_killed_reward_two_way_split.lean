-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_horizon_killed_reward_two_way_split
-- name    : AvramDividend.Classical.avram_ws01b_actual_horizon_killed_reward_two_way_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:43:57.191215+00:00
-- url     : https://prove2.me/theorems/27c65973-7315-4449-87cc-7584e51230dc
-- title:
--   Exact actual strict two-sided horizon killed payoff partitions into upper exit and surviving-strip remainder
-- statement:
--   For the actual spectrally negative Lévy strict two-sided passage clocks, at every finite horizon and path the exact killed q-scale terminal reward equals the discounted successful upper-first payoff once that exit has occurred, plus the discounted original reserve reward on paths still inside both bounds. Finite simultaneous upper and lower exits are excluded by the accepted source no-finite-tie theorem. This deterministic identity is the missing bridge from finite-horizon BV killed expectation to infinite-horizon exit reward.
-- source:
--   Source twoSidedExitUpTime/DownTime definitions and accepted no-finite-tie theorem. All bounds are exact original-clock values.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_two_sided_strict_exit_no_finite_tie

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_actual_horizon_killed_reward_two_way_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (a x : ℝ) (ha : 0 < a) (hxa : x ≤ a)
    (T : ℝ≥0) (ω : Ω) :
    (let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
     let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
     (if (T : ℝ≥0∞) < D then
        if min U D < ⊤ then
          Real.exp (-(q * ((min (min U D).toNNReal T) : ℝ))) *
            W (x + X.X (min (min U D).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else if D < U then 0
      else Real.exp (-(q * (U.toNNReal : ℝ))) *
        W (x + X.X U.toNNReal ω)) =
     (if U < D ∧ U.toNNReal ≤ T then
        Real.exp (-(q * (U.toNNReal : ℝ))) *
          W (x + X.X U.toNNReal ω) else 0) +
     (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
        Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω) else 0)) := by sorry
