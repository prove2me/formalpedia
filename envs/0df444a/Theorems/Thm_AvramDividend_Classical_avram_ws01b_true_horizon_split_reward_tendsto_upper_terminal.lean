-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_horizon_split_reward_tendsto_upper_terminal
-- name    : AvramDividend.Classical.avram_ws01b_true_horizon_split_reward_tendsto_upper_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T14:12:21.967828+00:00
-- url     : https://prove2.me/theorems/dfef2895-56d8-490f-93f7-f2d7666b304b
-- title:
--   Original killed stopped horizon reward converges to true upper-first payoff
-- statement:
--   On every true original spectrally negative Lévy sample path, the source finite-horizon completed-up-exit plus surviving qscale reward converges at growing natural horizons to the genuine upper-first discounted source terminal payoff; handles finite upper/lower exits and the never-exit atom.
-- source:
--   Canonical original no-finite-tie and never-exit discounted scale decay, finite first-exit clock exhaustion at natural horizons.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_never_exit_discounted_scale_decay
import Theorems.Thm_AvramDividend_Classical_chat04_two_sided_strict_exit_no_finite_tie

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_true_horizon_split_reward_tendsto_upper_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) :
    Tendsto (fun n : ℕ =>
      let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
      let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
      (if U < D ∧ U.toNNReal ≤ (n : ℝ≥0) then
        Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
      else 0) +
      (if ((n : ℝ≥0) : ℝ≥0∞) < U ∧ ((n : ℝ≥0) : ℝ≥0∞) < D then
        Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω)
      else 0)) atTop
      (𝓝 (if twoSidedExitUpTime X (a-x) ω <
          twoSidedExitDownTime X (-x) ω then
        Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
          W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
      else 0)) := by sorry
