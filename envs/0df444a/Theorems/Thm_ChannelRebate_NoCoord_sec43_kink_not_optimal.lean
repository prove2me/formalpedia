-- Prove2me | Theorems.Thm_ChannelRebate_NoCoord_sec43_kink_not_optimal
-- name    : ChannelRebate.NoCoord.sec43_kink_not_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:13.890869+00:00
-- url     : https://prove2.me/theorems/9e9492fc-ab55-4a49-8b56-2accd49aacf0
-- title:
--   §4.3, p. 1001 — for T > 0, no optimal effort–quantity pair of the retailer has effort exactly T/τ
-- statement:
--   In the setting of Lemma 2 (wholesale price $w < p$, rebate $u > 0$, return credit $s \le b < w$, demand $e\xi$ with a density positive on $[0,\infty)$ and finite mean, effort cost $V$ as in Assumption A5 and differentiable on $(0,\infty)$), let the target be strictly positive, $T > 0$, and let $\underline Q_0$, $\underline Q_1$ and $\tau$ be as in Lemma 2. Then no pair $(Q, T/\tau)$ maximizes the retailer's profit $R(Q, e \mid T)$ over $Q \ge 0$, $e \ge 0$:
--   $$\text{for every } Q,\quad (Q,\ T/\tau) \notin \arg\max_{Q' \ge 0,\ e' \ge 0} R(Q', e' \mid T).$$
--
--   The paper derives this from the convex kink of the retailer's effort objective $A(e \mid T) = \max_{Q \ge 0} R(Q, e \mid T)$ at $e = T/\tau$, where the left derivative is strictly smaller than the right derivative. The proof of Proposition 2 uses it to rule out the knife-edge effort level.
--
--   **Formalization Note** The statement records the consequence the paper draws ("$T/\tau$ cannot be the optimal effort level"), not the inequality of one-sided derivatives itself. The case $T = 0$ is excluded because then $T/\tau = 0$ and no kink exists. The derivative of $V$ at $T/\tau > 0$ comes from the effort-cost structure.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1001, §4.3 (display of A(e|T) and the one-sided derivative inequality)

import Mathlib
import Definitions.Def_ChannelRebate_NoCoord_Setting

open MeasureTheory ProbabilityTheory

namespace ChannelRebate.NoCoord

theorem sec43_kink_not_optimal (p s w u b T : ℝ) (hwp : w < p) (hu : 0 < u)
    (hsb : s ≤ b) (hbw : b < w) (hT : 0 < T)
    (D : Demand) (V : EffortCost)
    (Q0 Q1 τ : ℝ) (hQ0_pos : 0 < Q0) (hQ0 : Phi D Q0 = (p - w) / (p - b))
    (hQ1_pos : 0 < Q1) (hQ1 : Phi D Q1 = (p + u - w) / (p + u - b))
    (hτ : τ ∈ Set.Icc Q0 Q1)
    (hfτ : quantityProfit p w u b D τ Q0 = quantityProfit p w u b D τ Q1) :
    ∀ Q : ℝ, ¬ ChannelRebate.Effort.IsOptimalPair (retailerProfit p w u b T D V) Q (T / τ) := by sorry

end ChannelRebate.NoCoord
