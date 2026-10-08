-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_kernel_upper_indicator
-- name    : AvramDividend.Classical.negative_jump_kernel_upper_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:32:49.057717+00:00
-- url     : https://prove2.me/theorems/67cd39af-fb4f-4ef3-9273-e1b9041a59bb
-- title:
--   Small compensated jumps dominate the canonical Laplace kernel on negative jumps
-- statement:
--   For any nonnegative Laplace parameter and negative real jump, the canonical Levy exponent jump kernel is at most the small negative-jump compensated kernel on (-1,0). Outside small jumps the large-jump kernel is exp(theta*y)-1<=0. This is the exact upper companion to the lower indicator estimate needed to squeeze the exponent in the finite-absolute-first-moment branch.
-- source:
--   Exact indicator case split at y=-1 and positivity/monotonicity of the real exponential, supporting the canonical AvramDividend.Classical non-Gaussian exponent proof.

import Mathlib

open MeasureTheory Set

theorem AvramDividend.Classical.negative_jump_kernel_upper_indicator
    (θ y : ℝ) (hθ : 0 ≤ θ) (hy : y < 0) :
    Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 : ℝ)) y ≤
      (Ioo (-1 : ℝ) 0).indicator
        (fun z : ℝ => Real.exp (θ * z) - 1 - θ * z) y := by sorry
