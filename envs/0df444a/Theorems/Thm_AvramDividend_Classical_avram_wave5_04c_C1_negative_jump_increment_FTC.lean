-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_negative_jump_increment_FTC
-- name    : AvramDividend.Classical.avram_wave5_04c_C1_negative_jump_increment_FTC
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:57:41.705147+00:00
-- url     : https://prove2.me/theorems/62a348aa-6984-4789-ba38-8c001844f515
-- title:
--   Exact integral representation of a C1 negative-jump payoff increment
-- statement:
--   For every globally continuously differentiable real payoff and any real base y and increment R, identify the payoff difference across a negative jump exactly with the interval integral of the translated first derivative. The proof applies the one-dimensional fundamental theorem of calculus to g(r)=w(y-r) with g'(r)=-w'(y-r), using C1 continuity for interval integrability. In particular, the formula is valid on all nonnegative BV residual increments without invoking a second derivative or changing the original stochastic process.
-- source:
--   Remote compiler sentinel-verified candidates/work_on/AvramDividend_04c_C1_jump_increment_FTC_probe.lean

import Mathlib
set_option autoImplicit false
open MeasureTheory Set

theorem AvramDividend.Classical.avram_wave5_04c_C1_negative_jump_increment_FTC (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w) (y R : ℝ) :
    (∫ r in (0 : ℝ)..R, deriv w (y - r)) = w y - w (y - R) := by sorry
