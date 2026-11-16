-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_half_affine_admissible_right_payment_exact_gradient
-- name    : AvramDividend.Classical.avram_bvb_obstruction_half_affine_admissible_right_payment_exact_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:36:46.344575+00:00
-- url     : https://prove2.me/theorems/31af473e-d577-4e7d-90b8-2c3520bfc2b8
-- title:
--   Half-unit positive affine candidate exactly finances every admissible nonnegative right dividend increment
-- statement:
--   Whenever a dividend right payment Δ is nonnegative and no greater than the current reserve r, the piecewise candidate w(z)=0 below zero and 1/2+z otherwise satisfies Δ≤w(r)−w(r−Δ). This is the exact source-independent scalar step for the original positive-cap hJump verification hypothesis.
-- source:
--   Nonnegative Δ and Δ≤r imply both r and r−Δ are nonnegative. On both points w is affine of slope one, so the w difference is exactly Δ.

import Mathlib

theorem AvramDividend.Classical.avram_bvb_obstruction_half_affine_admissible_right_payment_exact_gradient (r Δ : ℝ) (hΔ : 0 ≤ Δ) (hBound : Δ ≤ r) :
    Δ ≤
      (if r < 0 then 0 else 1 / 2 + r) -
      (if r - Δ < 0 then 0 else 1 / 2 + (r - Δ)) := by sorry
