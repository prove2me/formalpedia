-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_caplinear_kink_true_physical_increment_Taylor_upper
-- name    : AvramDividend.Classical.avram_ga_original_caplinear_kink_true_physical_increment_Taylor_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T22:34:31.680995+00:00
-- url     : https://prove2.me/theorems/22f6f3eb-775a-409a-adab-c4ee3b104c6e
-- title:
--   Actual physical Gaussian increment caplinear Taylor residual bounded by tangent-extension residual across the kink
-- statement:
--   For any value function w and any original physical reserve y and raw increment z (including increments that cross the finite cutoff b in either direction), write the actual upper cap-linear extension with slope one above b, and the tangent extension with slope alpha>=1 above b. At the original pre-step reserve the coefficient is deriv w y at and below b, and respectively 1 and alpha strictly above b. The complete first-order spatial Taylor residual for the actual cap-linear test is no greater than the residual for the C1 tangent extension. The result handles crossing increments pathwise, without assuming Brownian regularity, approximating jumps, or taking an absolute value of the negative cap-local-time residual.
-- source:
--   Noncircular first-order signed cap-kink crossing inequality for original 0ef5d778 finite physical stopped Ito-Stieltjes estimate. It isolates the exact residual direction missing from the rootward Gaussian source.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_caplinear_kink_true_physical_increment_Taylor_upper
    (w : ℝ → ℝ) (b α y z : ℝ) (hα : 1 ≤ α) :
    ((if y + z ≤ b then w (y + z) else w b + (y + z - b)) -
      (if y ≤ b then w y else w b + (y - b)) -
        (if y ≤ b then deriv w y else 1) * z) ≤
    ((if y + z ≤ b then w (y + z) else w b + α * (y + z - b)) -
      (if y ≤ b then w y else w b + α * (y - b)) -
        (if y ≤ b then deriv w y else α) * z) := by sorry
