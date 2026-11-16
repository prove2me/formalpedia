-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_horizon_discounted_cash_terminal_lower_gt_boundary
-- name    : AvramDividend.Classical.avram_bvb_obstruction_tenth_horizon_discounted_cash_terminal_lower_gt_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:28:51.388979+00:00
-- url     : https://prove2.me/theorems/f1743793-f758-440d-afed-41c431863a1b
-- title:
--   At a tenth-unit nojump horizon discounted unit drift cash plus half-unit terminal exceeds the initial half-unit boundary
-- statement:
--   At T=1/10, the lower bound e^(−T)(T+1/2) for a unit-linear dividend path plus survival terminal is strictly greater than the original candidate w(0)=1/2. This is an explicit strict numerical contradiction to the drift-only positive-part cash budget on the original nojump zero-barrier event.
-- source:
--   The pinned inequality 1+x≤exp(x) gives exp(−1/10)≥9/10. Therefore (1/10+1/2)*exp(−1/10)≥(3/5)*(9/10)=27/50>1/2. The same strict gap is obtained on a positive-probability original nojump event once the original Stieltjes cash lower bound is proved.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
open Real

theorem AvramDividend.Classical.avram_bvb_obstruction_tenth_horizon_discounted_cash_terminal_lower_gt_boundary :
    (1 / 2 : ℝ) <
      (1 / 10 + 1 / 2) * Real.exp (-(1 / 10 : ℝ)) := by sorry
