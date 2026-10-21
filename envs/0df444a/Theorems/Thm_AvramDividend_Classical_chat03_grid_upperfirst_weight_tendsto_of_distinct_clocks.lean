-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_weight_tendsto_of_distinct_clocks
-- name    : AvramDividend.Classical.chat03_grid_upperfirst_weight_tendsto_of_distinct_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:00:00.821133+00:00
-- url     : https://prove2.me/theorems/d13d61af-fb6d-4724-bcab-428de14be63b
-- title:
--   Discounted first-passage grid rewards converge whenever the limiting two passage times are distinct
-- statement:
--   For two ENNReal grid clocks converging to separate limiting first-passage times and any real discount q, if the limiting clocks are unequal, the conditional upper-first discount converges to the corresponding limiting upper-first discounted reward. A strictly winning upper clock is finite, and the upper-first case follows by continuous exponential discount composition. If the lower clock wins, the upper-first grid reward is eventually zero. The both-infinite and finite-tie configurations are explicitly excluded, because conditional first-to-pass rewards can be discontinuous at ties.
-- source:
--   Accepted Chat 03 strict upper-first and lower-first payoff convergence theorems, UUIDs d2499db2-d52b-4186-8b21-0c9f85cc1216 and 94bd4886-60d0-4367-b8e4-7c8f420bab60.

import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_weight_eventually_zero_on_lowerfirst
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_weight_tendsto_on_upperfirst

open Filter Topology AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.chat03_grid_upperfirst_weight_tendsto_of_distinct_clocks
    (q : ℝ) (up down : ℝ≥0∞)
    (upGrid downGrid : ℕ → ℝ≥0∞)
    (hu : Tendsto upGrid atTop (𝓝 up))
    (hd : Tendsto downGrid atTop (𝓝 down))
    (hne : up ≠ down) :
    Tendsto
      (fun n => if upGrid n < downGrid n then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (upGrid n))))
      else 0) atTop
      (𝓝 (if up < down then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
      else 0)) := by sorry
