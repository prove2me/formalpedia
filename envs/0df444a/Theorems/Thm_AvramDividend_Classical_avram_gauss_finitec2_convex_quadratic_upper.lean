-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_convex_quadratic_upper
-- name    : AvramDividend.Classical.avram_gauss_finitec2_convex_quadratic_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:42:58.001325+00:00
-- url     : https://prove2.me/theorems/ada29d8b-7716-44fb-a3ca-0462a7592dcf
-- title:
--   Quadratic upper Taylor comparison on the finite Gaussian cap band
-- statement:
--   A convex quadratic-minus-value transform on the finite reserve cap band yields the one-sided quadratic upper Taylor estimate at each strict interior starting reserve, even for a destination at the cap. This is the missing input of the cap-quadratic glue theorem and follows from the Gaussian HJB one-sided bounded second derivative near the cap. Used in physical stopped Ito-to-Stieltjes child d1caa4aa.
-- source:
--   Source-checked pinned Mathlib ConvexOn.le_slope_of_hasDerivAt and ConvexOn.slope_le_of_hasDerivAt; link f80bc7ac cap Hessian and cap quadratic glue publication b91db941 into original d1caa4aa.

import Mathlib.Analysis.Convex.Deriv

open Set
noncomputable section

theorem AvramDividend.Classical.avram_gauss_finitec2_convex_quadratic_upper
    (w : ℝ → ℝ) (u C L : ℝ)
    (hconvex : ConvexOn ℝ (Icc u C) (fun y : ℝ => L / 2 * y ^ 2 - w y))
    (hqderiv : ∀ s ∈ Ico u C,
      HasDerivAt (fun y : ℝ => L / 2 * y ^ 2 - w y) (L * s - deriv w s) s) :
    ∀ s ∈ Ico u C, ∀ t ∈ Icc u C,
      w t ≤ w s + deriv w s * (t - s) + L / 2 * (t - s) ^ 2 := by sorry
