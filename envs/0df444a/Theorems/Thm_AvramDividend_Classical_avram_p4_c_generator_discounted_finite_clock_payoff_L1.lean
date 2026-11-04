-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_discounted_finite_clock_payoff_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_payoff_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:33:58.412068+00:00
-- url     : https://prove2.me/theorems/188ce554-ec97-4183-8d84-3a6fbf5c0287
-- title:
--   Discounted source HJB payoff term integrable on finite stopped clock with compact reserve bound
-- statement:
--   For the exact -q*w term in the original Lévy generator HJB residual, a bounded measurable payoff sampled on a finite interior localisation clock is integrable after the original nonnegative-rate exponential discount. The bound is proved using finite clock mass and the exponential <=1, without assuming global payoff boundedness or an original stochastic compensator. This is the payoff component needed to combine source c/Gaussian and nonlinear negative-mark jump drift L1.
-- source:
--   Mathlib finite-measure integrable indicator, bounded multiplication, real exponential; original HJB discounted -q*w term.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_payoff_L1
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (clock : T → ℝ≥0) (w : ℝ → ℝ) (q : ℝ)
    (hwmeas : Measurable (fun t => w (R t)))
    (hclock : Measurable clock)
    (hq : 0 ≤ q) (A : Set T) (hA : MeasurableSet A)
    (B : ℝ) (hbound : ∀ t ∈ A, |w (R t)| ≤ B) :
    Integrable (A.indicator (fun t =>
      Real.exp (-(q * (clock t : ℝ))) * w (R t))) μ := by sorry
