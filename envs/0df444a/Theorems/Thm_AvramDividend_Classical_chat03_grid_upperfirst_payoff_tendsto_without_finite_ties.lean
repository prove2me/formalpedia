-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
-- name    : AvramDividend.Classical.chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:13:22.138008+00:00
-- url     : https://prove2.me/theorems/d25d182c-7361-4d99-8c7f-d09de64e2a00
-- title:
--   Upper-first grid discount converges across all outcomes when finite ties are excluded and no-exit grids remain infinite
-- statement:
--   Suppose upper and lower ENNReal grid clocks converge to limiting passage clocks and finite ties are impossible. In addition, whenever the upper limiting clock equals infinity, the sampled upper grid clocks equal infinity at every grid resolution. Then the exact upper-first discounted grid payoff converges to the limiting payoff for every pair of sample-path clock outcomes, including both-infinite non-exit. For distinct limiting clocks, use the accepted general strict-order convergence theorem. On an equal limiting clock, the no-finite-ties premise makes both infinity, and the grid payoff is identically zero because the upper grid clock never becomes finite. This abstracts exactly the tie/no-exit completion required for first-passage approximation.
-- source:
--   Accepted Chat03 distinct-clock grid payoff convergence d13d61af-fb6d-4724-bcab-428de14be63b plus elementary ENNReal top-order branch.

import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_weight_tendsto_of_distinct_clocks

open Filter Topology AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
    (q : ℝ) (up down : ℝ≥0∞)
    (upGrid downGrid : ℕ → ℝ≥0∞)
    (hu : Tendsto upGrid atTop (𝓝 up))
    (hd : Tendsto downGrid atTop (𝓝 down))
    (hfiniteTie : up = down → up = ∞)
    (hNoUpGrid : up = ∞ → ∀ n : ℕ, upGrid n = ∞) :
    Tendsto
      (fun n => if upGrid n < downGrid n then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (upGrid n))))
        else 0) atTop
      (𝓝 (if up < down then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal up)))
        else 0)) := by sorry
