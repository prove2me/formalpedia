-- Prove2me | Theorems.Thm_ChannelRebate_Quantity_sec32_retailer_optimal_profit
-- name    : ChannelRebate.Quantity.sec32_retailer_optimal_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:17.459283+00:00
-- url     : https://prove2.me/theorems/eee188b7-e012-4a83-85aa-066a765aa9ff
-- title:
--   §3.2, p. 996 — the retailer's profit is (p+u−s)Γ(Q₁) − u(Γ(T)+T[1−Φ(T)]) if T < τ₀ and (p−s)Γ(Q₀) if T ≥ τ₀
-- statement:
--   In the setting of Lemma 1 ($0<c<w<p$, $s<c$, $u>0$, $Q_0, Q_1 > 0$ with $\Phi(Q_0) = (p-w)/(p-s)$ and $\Phi(Q_1) = (p+u-w)/(p+u-s)$), let $\tau_0 \in [Q_0,Q_1]$ satisfy $r(Q_0\mid\tau_0) = r(Q_1\mid\tau_0)$, and let $T \ge 0$. Then the retailer's optimal profit under the target rebate $(w,u,T)$ is
--   $$
--   r = \begin{cases} (p+u-s)\Gamma(Q_1) - u\big(\Gamma(T) + T[1-\Phi(T)]\big) & T < \tau_0,\\ (p-s)\Gamma(Q_0) & T \ge \tau_0. \end{cases}
--   $$
--   Precisely: if $T < \tau_0$, then $Q_1$ is an optimal order and $r(Q_1\mid T)$ equals the first expression; if $T \ge \tau_0$, then $Q_0$ is an optimal order and $r(Q_0\mid T)$ equals the second.
--
--   This closed form is what turns the coordination requirement of Theorem 1 into the scalar equation (1) for the target.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 996, §3.2 (display of the retailer profit under a target rebate)

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts
import Definitions.Def_ChannelRebate_Quantity_Setting
open MeasureTheory

namespace ChannelRebate.Quantity

/-- Taylor (2002), §3.2, display on p. 996. The retailer's profit under a target rebate is
`(p + u − s)Γ(Q₁) − u(Γ(T) + T[1 − Φ(T)])` if `T < τ₀` and `(p − s)Γ(Q₀)` if `T ≥ τ₀`,
attained at the optimal order `Q₁`, respectively `Q₀`. -/
theorem sec32_retailer_optimal_profit (p c s w u : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p)
    (hsc : s < c) (hu : 0 < u) (D : Demand)
    (Q0 : ℝ) (hQ0 : 0 < Q0) (hΦ0 : Phi D Q0 = (p - w) / (p - s))
    (Q1 : ℝ) (hQ1 : 0 < Q1) (hΦ1 : Phi D Q1 = (p + u - w) / (p + u - s))
    (τ0 : ℝ) (hτ0 : τ0 ∈ Set.Icc Q0 Q1)
    (hf0 : retailerProfit p s w u τ0 D Q0 - retailerProfit p s w u τ0 D Q1 = 0)
    (T : ℝ) (hT : 0 ≤ T) :
    (T < τ0 → IsOptimalOrder (retailerProfit p s w u T D) Q1 ∧
      retailerProfit p s w u T D Q1 =
        (p + u - s) * Gam D Q1 - u * (Gam D T + T * (1 - Phi D T))) ∧
    (τ0 ≤ T → IsOptimalOrder (retailerProfit p s w u T D) Q0 ∧
      retailerProfit p s w u T D Q0 = (p - s) * Gam D Q0) := by sorry

end ChannelRebate.Quantity
