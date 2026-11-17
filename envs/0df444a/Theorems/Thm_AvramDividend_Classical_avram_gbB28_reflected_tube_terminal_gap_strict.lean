-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB28_reflected_tube_terminal_gap_strict
-- name    : AvramDividend.Classical.avram_gbB28_reflected_tube_terminal_gap_strict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T11:36:09.698613+00:00
-- url     : https://prove2.me/theorems/14f087a8-b808-4dc8-bf18-e5b58f662007
-- title:
--   Strict deterministic cash-gap violation on reflected Brownian tube
-- statement:
--   For the explicit no-jump Gaussian parameters c=1, sigma=2, discount=1, cap=2/5, cutoff=1/5 and horizon T=2/5, the discounted caplinear cash-source lower bound strictly exceeds the permitted fixed-j cap defect whenever the terminal reserve is between 19/50 and 2/5. This is a deterministic conditional ingredient for an eventual stochastic counterexample; does not itself refute the source theorem.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_gbB28_reflected_tube_terminal_gap_strict
    (y : ℝ) (hylo : (19 / 50 : ℝ) ≤ y) (hyhi : y ≤ (2 / 5 : ℝ)) :
    (11 / 25 : ℝ) * (1 - Real.exp (-(2 / 5 : ℝ))) +
      Real.exp (-(2 / 5 : ℝ)) * (y - y ^ 2 - (4 / 25 : ℝ)) -
        (2 / 25 : ℝ) > (2 / 25 : ℝ) := by sorry
