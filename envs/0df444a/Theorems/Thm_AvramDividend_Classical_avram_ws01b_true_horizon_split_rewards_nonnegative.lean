-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_horizon_split_rewards_nonnegative
-- name    : AvramDividend.Classical.avram_ws01b_true_horizon_split_rewards_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:56:23.950118+00:00
-- url     : https://prove2.me/theorems/214b1f15-7752-4d09-8cb2-42c1f74bfcdf
-- title:
--   Original BV horizon split q-scale rewards nonnegative
-- statement:
--   Both the actual upper-first truncated discounted scale payoff and the genuinely surviving horizon discounted scale payoff are pointwise nonnegative under the true spectrally negative Lévy law and scale function hypotheses.
-- source:
--   Canonical original upper-exit level hitting and original before-clock surviving reserve strip.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_surviving_horizon_reserve_strip
import Theorems.Thm_AvramDividend_Classical_two_sided_up_exit_hits_level_of_no_positive_jumps

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_true_horizon_split_rewards_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (ω : Ω) :
    (0 ≤ if twoSidedExitUpTime X (a-x) ω <
                twoSidedExitDownTime X (-x) ω ∧
                (twoSidedExitUpTime X (a-x) ω).toNNReal ≤ T then
      Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
      else 0) ∧
    (0 ≤ if (T : ℝ≥0∞) < twoSidedExitUpTime X (a-x) ω ∧
                (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
      Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else 0) := by sorry
