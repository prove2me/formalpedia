-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_weight_tendsto_on_upperfirst
-- name    : AvramDividend.Classical.chat03_grid_upperfirst_weight_tendsto_on_upperfirst
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:10:37.187973+00:00
-- url     : https://prove2.me/theorems/d2499db2-d52b-4186-8b21-0c9f85cc1216
-- title:
--   Exact upper-first grid-discount convergence at a strictly winning upper passage
-- statement:
--   If upper and lower ENNReal grid passage clocks converge and the limiting upper clock strictly precedes the lower clock, the exact upper-first grid discount payoff converges to exp(-q times the finite limiting upper passage), coerced into ENNReal. Strict separation persists on sufficiently fine grids; upper passage finiteness gives continuity of ENNReal.toReal at the winning clock, and exponential, multiplication, negation and ENNReal.ofReal preserve limits. The lower limiting clock may be infinite. This is the upper-side grid-to-continuous payoff convergence needed for the stopped-scale identity.
-- source:
--   Pinned Mathlib Filter.Tendsto.eventually_lt, ENNReal.continuousAt_toReal, ENNReal.continuous_ofReal, Real.continuous_exp.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.chat03_grid_upperfirst_weight_tendsto_on_upperfirst
    (q : ℝ) (up down : ℝ≥0∞)
    (upGrid downGrid : ℕ → ℝ≥0∞)
    (hu : Tendsto upGrid atTop (𝓝 up))
    (hd : Tendsto downGrid atTop (𝓝 down))
    (hupper : up < down) :
    Tendsto
      (fun n => if upGrid n < downGrid n then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (upGrid n))))
        else 0) atTop
      (𝓝 (ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal up))))) := by sorry
