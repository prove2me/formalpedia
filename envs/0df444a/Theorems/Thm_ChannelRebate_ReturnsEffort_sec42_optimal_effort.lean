-- Prove2me | Theorems.Thm_ChannelRebate_ReturnsEffort_sec42_optimal_effort
-- name    : ChannelRebate.ReturnsEffort.sec42_optimal_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:44.356009+00:00
-- url     : https://prove2.me/theorems/14546986-61a6-4b15-9c81-9b2a68b30d4c
-- title:
--   §4.2, p. 1000 — under returns alone an optimal pair with e̲ > 0 has V′(e̲) = (p − b)Γ(Q̲₀), Q = e̲Q̲₀ and profit Λ(e̲), and conversely
-- statement:
--   Let $0<c<w<p$ and $s<c$ (Assumption A1), let $\xi$ have a density $\varphi$ satisfying Assumption A4, and let $V$ satisfy Assumption A5 and be differentiable on $(0,\infty)$ with derivative $V'$. Let the return credit be $b\in[s,w)$, let $\underline{Q}_0>0$ solve $\Phi(\underline{Q}_0)=(p-w)/(p-b)$, and write $\Lambda(\gamma)=\gamma V'(\gamma)-V(\gamma)$. Consider the retailer's profit under returns, $\underline{R}_b(Q,e)=-wQ+pE\min(Q,e\xi)+bE(Q-e\xi)^+-V(e)$, maximized jointly over $Q\ge 0$, $e\ge 0$.
--
--   1. If $(Q,\underline{e})$ is an optimal pair with $\underline{e}>0$, then
--   $$V'(\underline{e})=(p-b)\,\Gamma(\underline{Q}_0),\qquad Q=\underline{e}\,\underline{Q}_0,\qquad \underline{R}_b(Q,\underline{e})=\Lambda(\underline{e}).$$
--   2. Conversely, if $e>0$ satisfies $V'(e)=(p-b)\Gamma(\underline{Q}_0)$, then $(e\underline{Q}_0,e)$ is an optimal pair.
--
--   This is the second half of the paper's solution of the retailer's problem under returns alone: the optimal effort is characterized by its first-order condition, and the retailer's optimal profit is $\underline{R}=\Lambda(\underline{e})$. Together with the comparison of these first-order conditions across return credits it underlies Proposition 4.
--
--   **Formalization Note** The paper writes $(\partial/\partial e)V(e)$ without stating that $V$ is differentiable; differentiability on $(0,\infty)$ is added as a hypothesis with derivative $V'$. The paper restricts attention to strictly positive effort (p. 1000), so part 1 assumes $\underline{e}>0$. Optimality is maximization over $Q\ge0$, $e\ge0$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1000, §4.2 (optimal effort e̲ with (∂/∂e)V(e)|_{e=e̲} = (p − b)Γ(Q̲₀), optimal order Q₂, R̲ = Λ(e̲)); Λ defined p. 999

import Mathlib
import Definitions.Def_ChannelRebate_ReturnsEffort_Setting

namespace ChannelRebate.ReturnsEffort

/-- Taylor (2002), §4.2, p. 1000: under returns alone with credit `b ∈ [s, w)`, an optimal
order–effort pair with positive effort `e̲` satisfies `V′(e̲) = (p − b) Γ(Q̲₀)`, orders
`e̲ Q̲₀` and earns `Λ(e̲)`; conversely every `e > 0` solving the first-order condition gives
the optimal pair `(e Q̲₀, e)`. -/
theorem sec42_optimal_effort (p c s w : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p)
    (hsc : s < c) (D : Demand) (V : EffortCost) (V' : ℝ → ℝ)
    (hV' : ∀ e > 0, HasDerivAt V.V (V' e) e) (b : ℝ) (hsb : s ≤ b) (hbw : b < w)
    (Q₀ : ℝ) (hQ₀ : 0 < Q₀) (hΦ : Phi D Q₀ = (p - w) / (p - b)) :
    (∀ Q e, IsOptimalPair (returnsProfit p w b D V) Q e → 0 < e →
        V' e = (p - b) * Gam D Q₀ ∧ Q = e * Q₀ ∧
          returnsProfit p w b D V Q e = Lam V V' e) ∧
      (∀ e, 0 < e → V' e = (p - b) * Gam D Q₀ →
        IsOptimalPair (returnsProfit p w b D V) (e * Q₀) e) := by sorry

end ChannelRebate.ReturnsEffort
