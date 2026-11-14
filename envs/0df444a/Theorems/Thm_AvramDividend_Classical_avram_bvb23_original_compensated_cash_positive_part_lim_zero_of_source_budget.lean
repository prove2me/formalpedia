-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_compensated_cash_positive_part_lim_zero_of_source_budget
-- name    : AvramDividend.Classical.avram_bvb23_original_compensated_cash_positive_part_lim_zero_of_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:47:31.544655+00:00
-- url     : https://prove2.me/theorems/b7ce23ad-4317-48d0-bf10-7d03ac69645c
-- title:
--   Original BV source compensated stopped cash positive error vanishes from convergent cash, negative-mark compensator and masked generator limits
-- statement:
--   Suppose the original finite-cap source discounted cash plus stopped reward converges to a finite physical limit f, the full original negative-mark compensator K converges to k, and the source strictly positive-interior generator sum G vanishes. If the exact source limiting compensated budget satisfies f at most the original candidate initial value minus k, then the positive part of the original finite mesh compensated error converges to zero. This exact algebraic limit closes the final positive-part step in the zero-mark survival and ruin branches once their source-specific cash, K and G convergence are established.
-- source:
--   Original ed067740/b0915396 error expression F_n-(w(x)+(-K_n+G_n)), pinned Filter.Tendsto.max and real positive-part continuity.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb23_original_compensated_cash_positive_part_lim_zero_of_source_budget
    (F K G : ℕ → ℝ) (w f k : ℝ)
    (hF : Tendsto F atTop (𝓝 f))
    (hK : Tendsto K atTop (𝓝 k))
    (hG : Tendsto G atTop (𝓝 (0 : ℝ)))
    (hBudget : f ≤ w - k) :
    Tendsto (fun n => max (F n - (w + ((-K n) + G n))) 0)
      atTop (𝓝 (0 : ℝ)) := by sorry
