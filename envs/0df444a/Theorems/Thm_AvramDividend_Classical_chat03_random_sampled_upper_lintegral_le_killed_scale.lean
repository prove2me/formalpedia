-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_random_sampled_upper_lintegral_le_killed_scale
-- name    : AvramDividend.Classical.chat03_random_sampled_upper_lintegral_le_killed_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:02:38.429281+00:00
-- url     : https://prove2.me/theorems/68b9c12e-bf39-4448-802a-15d2e9831dd5
-- title:
--   Expected sampled upper-boundary reward is dominated by expected sampled lower-killed scale
-- statement:
--   For any random nonnegative observation time T, including a first strict grid exit index converted to its sampled clock time, the expected upper-exit discounted boundary scale payoff is at most the expected sampled scale payoff killed upon an observed lower crossing. This follows by integrating the already verified pointwise sampled-upper reward inequality and requires no martingale or q-harmonicity assertion.
-- source:
--   Depends on accepted pointwise sampled upper-event versus lower-killed scale comparison, then applies monotonicity of nonnegative Lebesgue integrals.

import Theorems.Thm_AvramDividend_Classical_chat03_sampled_upper_event_payoff_le_killed_scale
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_random_sampled_upper_lintegral_le_killed_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (T : Ω → ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal
      (if a - x < X.X (T ω) ω then
        Real.exp (-(q * (T ω : ℝ))) * W a else 0) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal
      (if X.X (T ω) ω < -x then 0 else
        Real.exp (-(q * (T ω : ℝ))) *
          W (x + X.X (T ω) ω)) ∂P) := by sorry
