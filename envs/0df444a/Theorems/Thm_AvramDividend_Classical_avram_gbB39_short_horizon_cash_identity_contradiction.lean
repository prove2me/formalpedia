-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB39_short_horizon_cash_identity_contradiction
-- name    : AvramDividend.Classical.avram_gbB39_short_horizon_cash_identity_contradiction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:39:42.573169+00:00
-- url     : https://prove2.me/theorems/945cc0b4-d2c0-4f14-b0fd-f9d166a85eaf
-- title:
--   Short-horizon exact reflected Gaussian cash identity contradicts fixed-j bound
-- statement:
--   For the short T=1/1000 reflected Gaussian tube, once the exact original pre-ruin discounted cash identity is supplied, the Proved B36 gap theorem yields a strict violation of the disputed positive-drift fixed-j pathwise upper bound. This is a deterministic conditional conclusion, not an unconditional stochastic disproof.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB36_short_horizon_sigma1_gap
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB39_short_horizon_cash_identity_contradiction
    (y F wC N : ℝ)
    (hylo : (5 / 44 : ℝ) ≤ y)
    (hyhi : y ≤ (1 / 8 : ℝ))
    (hCash : F - wC - N =
      (193419 / 968 : ℝ) * (1 - Real.exp (-(1 / 100000 : ℝ))) +
      Real.exp (-(1 / 100000 : ℝ)) *
        (y - 4 * y ^ 2 - 15 / 242) - (1 / 1936 : ℝ)) :
    ¬ F - wC ≤ N + (1 / 1936 : ℝ) := by sorry
