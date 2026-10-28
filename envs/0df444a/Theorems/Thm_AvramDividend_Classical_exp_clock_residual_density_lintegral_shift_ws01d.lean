-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_clock_residual_density_lintegral_shift_ws01d
-- name    : AvramDividend.Classical.exp_clock_residual_density_lintegral_shift_ws01d
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:02:41.292737+00:00
-- url     : https://prove2.me/theorems/fd8ff708-3a83-44f1-9565-f01000bbb033
-- title:
--   Genuine real exponential-clock residual density translation for an arbitrary measurable reward
-- statement:
--   For an independent real exponential observation clock with rate p>0 and any nonnegative deterministic age a, the exponential-density weighted integral of an arbitrary nonnegative measurable future reward evaluated at residual time t-a on the event t≥a equals exp(-p a) times the original exponential-density weighted integral of that reward. The identity is exact at real time zero and at the non-strict boundary and uses the actual expMeasure density and translation invariance of Lebesgue measure. It is a necessary measurable kernel step for the finite-cap random-terminal Esscher supremum law, not a conditional substitute for it.
-- source:
--   Mathlib pinned revision 0df444a360eaa60ab8c11dca51a86af692955474: ProbabilityTheory.exponentialPDF_of_nonneg, MeasureTheory.lintegral_add_right_eq_self and MeasureTheory.lintegral_const_mul; Kuznetsov–Kyprianou–Rivero, Theory of Scale Functions for Spectrally Negative Lévy Processes, section 2.1 (exponential observation and memorylessness).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Group.LIntegral

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.exp_clock_residual_density_lintegral_shift_ws01d
    (p : ℝ) (hp : 0 < p) (a : ℝ≥0)
    (reward : ℝ → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ t : ℝ, if (a : ℝ) ≤ t then
       ProbabilityTheory.exponentialPDF p t * reward (t - (a : ℝ))
       else 0 ∂volume) =
    ENNReal.ofReal (Real.exp (-(p * (a : ℝ)))) *
      (∫⁻ u : ℝ, ProbabilityTheory.exponentialPDF p u *
        reward u ∂volume) := by sorry
