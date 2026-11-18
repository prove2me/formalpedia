-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB35_cash_identity_forces_strict_excess
-- name    : AvramDividend.Classical.avram_gbB35_cash_identity_forces_strict_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:28:42.855657+00:00
-- url     : https://prove2.me/theorems/7a619020-5993-48b6-85c0-08bb5ed423ef
-- title:
--   Gaussian stopped cash identity forces strict excess over fixed-band bound
-- statement:
--   Under the exact positive Gaussian stopped cash identity and terminal reserve within the upper strip, the previously Proved B30 scalar bound contradicts a fixed-j pathwise cash upper bound. Conditional on the missing stochastic cash identity; does not disprove the original target.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_sigma1_halfband_discounted_strict_gap
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB35_cash_identity_forces_strict_excess
    (y F wC N : ℝ)
    (hylo : (5 / 44 : ℝ) ≤ y)
    (hyhi : y ≤ (1 / 8 : ℝ))
    (hCash : F - wC - N =
      (193419 / 968 : ℝ) * (1 - Real.exp (-(1 / 40000 : ℝ))) +
      Real.exp (-(1 / 40000 : ℝ)) * (y - 4 * y ^ 2 - 15 / 242) -
      (1 / 1936 : ℝ)) :
    ¬ F - wC ≤ N + (1 / 1936 : ℝ) := by sorry
