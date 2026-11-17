-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB30_sigma1_halfband_discounted_strict_gap
-- name    : AvramDividend.Classical.avram_gbB30_sigma1_halfband_discounted_strict_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T13:31:51.603781+00:00
-- url     : https://prove2.me/theorems/d8e559ab-18b5-4270-b2e8-214f44afb974
-- title:
--   Unit-volatility reflected-Gaussian strict discounted cutoff tube gap
-- statement:
--   Under c=2, Gaussian coefficient 1, q=1/100, cap C=1/8, j=9 cutoff b=5/44, reward w(y)=2y-4y² and horizon T=1/400, prove that the lower bound on the affine continuation generator integral plus positive terminal defect exceeds twice fixed-band cap-linear gap 1/1936. This is algebraic only and does not assert an unverified stochastic source or probability theorem.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_gbB30_sigma1_halfband_discounted_strict_gap
    (y : ℝ) (hylo : (5 / 44 : ℝ) ≤ y)
    (hyhi : y ≤ (1 / 8 : ℝ)) :
    ((193419 / 968 : ℝ) *
        (1 - Real.exp (-(1 / 40000 : ℝ))) +
      Real.exp (-(1 / 40000 : ℝ)) *
        (y - 4 * y ^ 2 - (15 / 242 : ℝ)) -
        (1 / 1936 : ℝ)) > (1 / 1936 : ℝ) := by sorry
