-- Prove2me | Theorems.Thm_ChannelRebate_ReturnsEffort_sec42_order_given_effort
-- name    : ChannelRebate.ReturnsEffort.sec42_order_given_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:45.35206+00:00
-- url     : https://prove2.me/theorems/50e95f17-0667-4f08-85ed-6d0305b90d4d
-- title:
--   §4.2, p. 1000 — under returns alone and fixed effort e > 0 the optimal order is uniquely Q₂ = eQ̲₀, with profit e(p − b)Γ(Q̲₀) − V(e)
-- statement:
--   Let $0<c<w<p$ and $s<c$ (Assumption A1), let the demand factor $\xi$ have a density $\varphi$ satisfying Assumption A4, and let $V$ satisfy Assumption A5. Let the return credit be $b\in[s,w)$ and fix an effort level $e>0$. Let $\underline{Q}_0>0$ be the critical fractile
--   $$\Phi(\underline{Q}_0)=\frac{p-w}{p-b},$$
--   i.e. $\underline{Q}_0=\Phi^{-1}((p-w)/(p-b))$. Then the retailer's profit under returns, $Q\mapsto \underline{R}_b(Q,e)=-wQ+pE\min(Q,e\xi)+bE(Q-e\xi)^+-V(e)$, has exactly one maximizer over $Q\ge 0$, namely
--   $$Q_2=e\,\underline{Q}_0,$$
--   and its value there is
--   $$\underline{R}_b(e\underline{Q}_0,e)=e\,(p-b)\,\Gamma(\underline{Q}_0)-V(e).$$
--
--   This is the first half of the paper's solution of the retailer's problem under returns alone: for each effort level, the optimal order scales linearly in the effort. The value formula is the first branch of the retailer's reduced profit $A(e\mid T)$ on p. 1001 with rebate $u=0$.
--
--   **Formalization Note** $\Phi^{-1}$ is not used as a function: $\underline{Q}_0$ is any positive solution of its defining equation, which is unique under A4. "The optimal order quantity is $Q_2$" is stated as equality of the set of maximizers over $Q\ge0$ with $\{e\underline{Q}_0\}$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1000, §4.2 (definition of Q̲₀ and Q₂ ≡ eQ̲₀; optimal order quantity Q₂); value: p. 1001, first branch of A(e|T) with u = 0

import Mathlib
import Definitions.Def_ChannelRebate_ReturnsEffort_Setting

namespace ChannelRebate.ReturnsEffort

/-- Taylor (2002), §4.2, p. 1000: under returns alone with credit `b ∈ [s, w)` and a fixed effort
`e > 0`, the retailer's unique optimal order is `Q₂ = e Q̲₀`, where `Φ(Q̲₀) = (p − w)/(p − b)`,
and her profit there is `e (p − b) Γ(Q̲₀) − V(e)`. -/
theorem sec42_order_given_effort (p c s w : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p)
    (hsc : s < c) (D : Demand) (V : EffortCost) (b : ℝ) (hsb : s ≤ b) (hbw : b < w)
    (e : ℝ) (he : 0 < e) (Q₀ : ℝ) (hQ₀ : 0 < Q₀) (hΦ : Phi D Q₀ = (p - w) / (p - b)) :
    optimalOrders (fun Q => returnsProfit p w b D V Q e) = {e * Q₀} ∧
      returnsProfit p w b D V (e * Q₀) e = e * (p - b) * Gam D Q₀ - V.V e := by sorry

end ChannelRebate.ReturnsEffort
