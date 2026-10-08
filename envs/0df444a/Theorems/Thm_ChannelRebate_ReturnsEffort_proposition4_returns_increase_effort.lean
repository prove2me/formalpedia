-- Prove2me | Theorems.Thm_ChannelRebate_ReturnsEffort_proposition4_returns_increase_effort
-- name    : ChannelRebate.ReturnsEffort.proposition4_returns_increase_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:43.141153+00:00
-- url     : https://prove2.me/theorems/ffe93b7b-b0d9-43b2-b64a-8adeebd3a839
-- title:
--   Proposition 4, p. 1004 — under A4 and A5 the retailer's optimal effort under returns alone is strictly increasing in the return credit b
-- statement:
--   Let $0<c<w<p$ and $s<c$ (Assumption A1). Let demand be $e\xi$, where $e\ge 0$ is the retailer's sales effort and $\xi$ has a density $\varphi$ with $\varphi(\xi)>0$ for all $\xi\ge0$ (Assumption A4). Let the effort cost $V$ be strictly convex and strictly increasing on $[0,\infty)$ with $V(0)=0$ (Assumption A5), and differentiable on $(0,\infty)$. Under a return credit $b$ the retailer chooses $Q\ge0$ and $e\ge 0$ to maximize
--   $$\underline{R}_b(Q,e)=-wQ+p\,E\min(Q,e\xi)+b\,E(Q-e\xi)^+-V(e).$$
--
--   Let $s\le b_2<b_1<w$, let $(Q_1,e_1)$ be an optimal pair under $b_1$ and $(Q_2,e_2)$ an optimal pair under $b_2$, and suppose $e_2>0$. Then
--   $$e_2<e_1 .$$
--
--   That is, the retailer's optimal effort under returns alone is strictly increasing in the return credit, the paper's $\partial\underline{e}/\partial b>0$. This reverses the conventional view that returns weaken a retailer's incentive for sales effort: for a fixed order quantity a larger credit lowers the marginal value of effort, but once the order quantity is re-optimized together with the effort, a larger credit raises effort.
--
--   **Formalization Note** The paper states $\partial\underline{e}/\partial b>0$ and its proof establishes strict monotonicity, which is what is formalized; a derivative would need $\underline{e}(b)$ to be differentiable, which A5 does not provide. Differentiability of $V$ on $(0,\infty)$ is added because the paper uses $V'$ in $\Lambda$ and in the first-order condition. Effort at the smaller credit is assumed positive, following the paper's restriction to strictly positive effort (p. 1000). Optimal pairs are maximizers over $Q\ge0$, $e\ge0$; their existence is a hypothesis, as on p. 999.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1004, Proposition 4 (context §4.4.2, p. 1003); proof: Appendix, p. 1006

import Mathlib
import Definitions.Def_ChannelRebate_ReturnsEffort_Setting

namespace ChannelRebate.ReturnsEffort

/-- Taylor (2002), Proposition 4, p. 1004 (proof p. 1006): under A4 and A5, the retailer's
optimal effort under returns alone is strictly increasing in the return credit. If
`s ≤ b₂ < b₁ < w` and `(Q₁, e₁)`, `(Q₂, e₂)` are optimal order–effort pairs under the credits
`b₁`, `b₂` with `e₂ > 0`, then `e₂ < e₁`. -/
theorem proposition4_returns_increase_effort (p c s w : ℝ) (hc : 0 < c) (hcw : c < w)
    (hwp : w < p) (hsc : s < c) (D : Demand) (V : EffortCost) (V' : ℝ → ℝ)
    (hV' : ∀ e > 0, HasDerivAt V.V (V' e) e) (b₁ b₂ : ℝ) (hs : s ≤ b₂) (h12 : b₂ < b₁)
    (hw : b₁ < w) (Q₁ e₁ Q₂ e₂ : ℝ) (h₁ : IsOptimalPair (returnsProfit p w b₁ D V) Q₁ e₁)
    (h₂ : IsOptimalPair (returnsProfit p w b₂ D V) Q₂ e₂) (he₂ : 0 < e₂) :
    e₂ < e₁ := by sorry

end ChannelRebate.ReturnsEffort
