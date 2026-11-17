-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB29_optimised_reflected_tube_discounted_gap_strict
-- name    : AvramDividend.Classical.avram_gbB29_optimised_reflected_tube_discounted_gap_strict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:39:46.297793+00:00
-- url     : https://prove2.me/theorems/e1c1ed37-fcc7-4851-9b6d-0b06d46330f5
-- title:
--   Optimised reflected Gaussian tube discounted strict cash gap
-- statement:
--   For c=2, sigma=2, q=1/100, cap C=1/2, fixed band b=5/11 (j=9), horizon T=1/400 and terminal reserve y in [5/11,1/2], the minimal discounted affine generator contribution plus the nonnegative terminal defect exceeds twice the fixed-band cap defect 1/484. This is an exact deterministic component of a candidate counterexample to an overly strong fixed-j pathwise inequality, not a stochastic counterexample itself.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_gbB29_optimised_reflected_tube_discounted_gap_strict
    (y : ℝ) (hylo : (5 / 11 : ℝ) ≤ y) (hyhi : y ≤ (1 / 2 : ℝ)) :
    ((200 : ℝ) - (181 / 242 : ℝ)) *
        (1 - Real.exp (-(1 / 40000 : ℝ))) +
      Real.exp (-(1 / 40000 : ℝ)) *
        (2 * y - y ^ 2 -
          ((85 / 121 : ℝ) + (y - (5 / 11 : ℝ)))) -
        (1 / 484 : ℝ) > (1 / 484 : ℝ) := by sorry
