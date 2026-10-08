-- Prove2me | Theorems.Thm_ChannelRebate_NoCoord_proposition2_no_single_instrument
-- name    : ChannelRebate.NoCoord.proposition2_no_single_instrument
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:19.05993+00:00
-- url     : https://prove2.me/theorems/babce25a-0b24-48d4-8750-f45c09b657a2
-- title:
--   Proposition 2, p. 1003 — returns alone, linear rebates alone or target rebates alone cannot coordinate effort and quantity
-- statement:
--   Let $0 < c < w < p$ and $s < c$ (Assumption A1). Demand is $e\xi$, where the retailer's effort is $e \ge 0$ and $\xi$ has a density $\varphi$ with $\varphi = 0$ on $(-\infty,0)$, $\varphi > 0$ on $[0,\infty)$ (Assumption A4) and finite mean. Effort costs $V(e)$, where $V(0) = 0$ and $V$ is strictly increasing and strictly convex on $[0,\infty)$ (Assumption A5) and differentiable on $(0,\infty)$. Let $(\bar Q, \bar e)$ maximize the integrated channel's profit
--   $$\Pi(Q, e) = -cQ + pE\min(Q, e\xi) + sE(Q - e\xi)^+ - V(e)$$
--   over $Q \ge 0$, $e \ge 0$, with $\bar e > 0$. Write the retailer's profit under wholesale price $w$, rebate $u$ per unit sold beyond the target $T$, and return credit $b$ per unsold unit as
--   $$R(Q, e \mid T) = -wQ + pE\min(Q, e\xi) + uE(\min(Q, e\xi) - T)^+ + bE(Q - e\xi)^+ - V(e).$$
--   Then $(\bar Q, \bar e)$ maximizes $R$ over $Q \ge 0$, $e \ge 0$ under none of the following contracts:
--
--   1. **returns alone**: $u = 0$ and any return credit $b \in [s, w)$;
--   2. **a linear rebate alone**: $T = 0$, any $u > 0$, and no returns ($b = s$);
--   3. **a target rebate alone**: any $T \ge 0$, any $u > 0$, and no returns ($b = s$).
--
--   In each case the retailer's optimal decisions cannot be the integrated channel's, so channel coordination in effort and quantity cannot be achieved. By contrast, the paper's Theorem 2 shows that a target rebate combined with returns can coordinate, and a linear rebate combined with returns coordinates only at $u = w - c$, $b = s + w - c$, which leaves the manufacturer no profit.
--
--   **Formalization Note** The existence of the integrated optimum is assumed in the paper in words (p. 999) and is a hypothesis here; its positivity $\bar e > 0$ is a disclosed hypothesis, because the paper's optimum is interior (characterized by first-order conditions) and with $\bar e = 0$ the channel would sell nothing. Differentiability of $V$ on $(0,\infty)$ is carried by the effort-cost structure: the paper's argument compares first-order conditions in $e$, and a kink of $V$ at $\bar e$ could otherwise let both the channel and the retailer stop at $\bar e$. "Not an optimal pair" is stronger than "the retailer's optimum is not unique or not $(\bar Q, \bar e)$": it excludes $(\bar Q, \bar e)$ from the retailer's maximizers altogether.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1003, Proposition 2; model p. 994 (A1, A4), p. 999 (A5, Π), p. 1000 (R(Q, e|T)); proof in the Appendix, p. 1006

import Mathlib
import Definitions.Def_ChannelRebate_NoCoord_Setting

open MeasureTheory ProbabilityTheory

namespace ChannelRebate.NoCoord

theorem proposition2_no_single_instrument (p c s w : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p)
    (hsc : s < c) (D : Demand) (V : EffortCost)
    (Qbar ebar : ℝ) (hopt : ChannelRebate.Effort.IsOptimalPair (chainProfit p c s D V) Qbar ebar) (hebar : 0 < ebar) :
    (∀ b : ℝ, s ≤ b → b < w →
      ¬ ChannelRebate.Effort.IsOptimalPair (retailerProfit p w 0 b 0 D V) Qbar ebar) ∧
    (∀ u : ℝ, 0 < u →
      ¬ ChannelRebate.Effort.IsOptimalPair (retailerProfit p w u s 0 D V) Qbar ebar) ∧
    (∀ u T : ℝ, 0 < u → 0 ≤ T →
      ¬ ChannelRebate.Effort.IsOptimalPair (retailerProfit p w u s T D V) Qbar ebar) := by sorry

end ChannelRebate.NoCoord
