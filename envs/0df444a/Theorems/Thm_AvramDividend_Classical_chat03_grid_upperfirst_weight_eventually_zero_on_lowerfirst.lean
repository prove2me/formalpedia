-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_weight_eventually_zero_on_lowerfirst
-- name    : AvramDividend.Classical.chat03_grid_upperfirst_weight_eventually_zero_on_lowerfirst
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:03:13.414686+00:00
-- url     : https://prove2.me/theorems/94bd4886-60d0-4367-b8e4-7c8f420bab60
-- title:
--   Upper-first grid discounts vanish eventually on paths with strictly earlier lower first passage
-- statement:
--   Let approximating upper and lower first-passage grid clocks converge individually in ENNReal to possibly infinite limit clocks. Whenever the limiting lower clock is strictly earlier than the upper clock, all sufficiently fine grids have lower passage strictly earlier too, so the exact upper-first discount weight is identically zero for every sufficiently fine grid, for any real q. This handles lower-first paths in the first-passage grid-to-continuous payoff convergence without assumptions of finite upper time, continuity of ENNReal.toReal at infinity, or attainment of the strict exit at its infimum.
-- source:
--   Pinned Mathlib Filter.Tendsto.eventually_lt, ENNReal ordering, verified using private remote elaboration probe at pinned revision.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Complex.Exponential

open Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.chat03_grid_upperfirst_weight_eventually_zero_on_lowerfirst
    (q : ℝ) (up down : ℝ≥0∞)
    (upGrid downGrid : ℕ → ℝ≥0∞)
    (hu : Tendsto upGrid atTop (𝓝 up))
    (hd : Tendsto downGrid atTop (𝓝 down))
    (hlower : down < up) :
    ∀ᶠ n in atTop,
      (if upGrid n < downGrid n then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (upGrid n))))
      else 0) = 0 := by sorry
