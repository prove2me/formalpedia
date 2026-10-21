-- Prove2me | Theorems.Thm_AvramDividend_Classical_grid_upperfirst_liminf_of_strict_order
-- name    : AvramDividend.Classical.grid_upperfirst_liminf_of_strict_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:54:51.160585+00:00
-- url     : https://prove2.me/theorems/674f4ad6-fdef-4558-a512-027419465fa1
-- title:
--   Exact upper-first discounted grid-payoff liminf for strictly ordered passage clocks
-- statement:
--   When approximate upper and lower first-passage clocks converge in extended nonnegative reals and the limiting clocks are strictly ordered, the upper-first discounted grid reward has liminf equal to the corresponding continuous-time upper-first reward. Combines two independently accepted Chat 03 convergence results, for upper-first and lower-first cases, with Tendsto.liminf_eq. It is the pathwise ingredient needed for Fatou to transport grid exponential bounds to first-passage rewards.
-- source:
--   Proved chat03_grid_upperfirst_weight_tendsto_on_upperfirst, chat03_grid_upperfirst_weight_eventually_zero_on_lowerfirst and pinned Mathlib Filter.Tendsto.liminf_eq.

import Mathlib
open Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.grid_upperfirst_liminf_of_strict_order
    (q : ℝ) (up down : ENNReal)
    (upGrid downGrid : ℕ → ENNReal)
    (hu : Tendsto upGrid atTop (nhds up))
    (hd : Tendsto downGrid atTop (nhds down))
    (hsep : up < down ∨ down < up) :
    (if up < down then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up))) else 0) =
      liminf (fun n => if upGrid n < downGrid n then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (upGrid n)))) else 0) atTop := by sorry
