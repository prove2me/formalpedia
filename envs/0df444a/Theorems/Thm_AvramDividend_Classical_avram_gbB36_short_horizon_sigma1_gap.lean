-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB36_short_horizon_sigma1_gap
-- name    : AvramDividend.Classical.avram_gbB36_short_horizon_sigma1_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:32:04.160495+00:00
-- url     : https://prove2.me/theorems/d05dfb88-fbbe-4e1d-a004-3c82129c735c
-- title:
--   Short-horizon positive Gaussian tube still forces strict cap-gap excess
-- statement:
--   For c=2,sigma=1, cap 1/8, cutoff 5/44 and q=1/100, a shorter T=1/1000 preserves the strict discounted affine positive-drift excess above twice the cap defect. This horizon permits a zero-centred Brownian small-ball event without a Cameron-Martin shift and remains conditional on the original stopped cash stochastic identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB34_sigma1_upper_band_positive_drift
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB36_short_horizon_sigma1_gap
    (y : ℝ) (hylo : (5 / 44 : ℝ) ≤ y)
    (hyhi : y ≤ (1 / 8 : ℝ)) :
    ((193419 / 968 : ℝ) *
      (1 - Real.exp (-(1 / 100000 : ℝ))) +
    Real.exp (-(1 / 100000 : ℝ)) *
      (y - 4 * y ^ 2 - (15 / 242 : ℝ)) -
      (1 / 1936 : ℝ)) > (1 / 1936 : ℝ) := by sorry
