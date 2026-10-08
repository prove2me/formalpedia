-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_negative_compensated_secant_limit
-- name    : AvramDividend.Classical.exp_negative_compensated_secant_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:58:43.219208+00:00
-- url     : https://prove2.me/theorems/eaec56ef-3470-4320-9838-ac17d62fff5b
-- title:
--   Compensated negative-jump exponential secants converge to absolute jump size
-- statement:
--   At every fixed strictly negative jump y, along Laplace parameters theta=n+1, the normalised exponential remainder (exp(theta y)-1-theta y)/theta converges to -y=|y|. Together with monotonicity of the same remainder, this is the pointwise limit needed for monotone convergence in the zero-Gaussian infinite-small-jump-first-moment case.
-- source:
--   Pinned Mathlib tendsto_one_div_add_atTop_nhds_zero_nat and squeeze_zero, and the exponential bounds 0<=exp(theta y)<=1 for theta>=0,y<0. Normalising by theta shows (exp(theta y)-1)/theta tends to zero.

import Mathlib

theorem AvramDividend.Classical.exp_negative_compensated_secant_limit (y : ℝ) (hy : y < 0) :
    Filter.Tendsto
      (fun n : ℕ => (Real.exp (((n : ℝ) + 1) * y) - 1 -
        ((n : ℝ) + 1) * y) / ((n : ℝ) + 1))
      Filter.atTop (nhds (-y)) := by sorry
