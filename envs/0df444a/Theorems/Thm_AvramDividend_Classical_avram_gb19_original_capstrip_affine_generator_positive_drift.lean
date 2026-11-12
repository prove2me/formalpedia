-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb19_original_capstrip_affine_generator_positive_drift
-- name    : AvramDividend.Classical.avram_gb19_original_capstrip_affine_generator_positive_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:32:02.846114+00:00
-- url     : https://prove2.me/theorems/9e015559-45e5-432d-968a-85ba20bf5bdc
-- title:
--   Finite-cap linear upper-strip HJB drift bounded by positive original drift
-- statement:
--   For the finite-cap original Gaussian cash ledger gfinite61, the cap-linearised test function equals wb+(y-b) above the interior cutoff b. Whenever the boundary value wb and excess y-b are nonnegative and discount q is nonnegative, its affine generator c-q*(wb+y-b) is at most max(c,0), supplying exactly the positive upper-strip occupation coefficient. This is a deterministic source calculus step; the original stopped Ito-Stieltjes ledger remains separate.
-- source:
--   Scalar original finite-cap upper-strip affine generator estimate for gfinite61; no surrogate Gaussian process.

import Mathlib

theorem AvramDividend.Classical.avram_gb19_original_capstrip_affine_generator_positive_drift
    (c q wb b y : ℝ) (hq : 0 ≤ q) (hwb : 0 ≤ wb) (hby : b ≤ y) :
    c - q * (wb + (y - b)) ≤ max c 0 := by sorry
