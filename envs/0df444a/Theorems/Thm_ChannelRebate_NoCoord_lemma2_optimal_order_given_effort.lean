-- Prove2me | Theorems.Thm_ChannelRebate_NoCoord_lemma2_optimal_order_given_effort
-- name    : ChannelRebate.NoCoord.lemma2_optimal_order_given_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:28.386038+00:00
-- url     : https://prove2.me/theorems/d5a6e187-d76a-4822-b610-411edcc52c42
-- title:
--   Lemma 2, p. 1000 — given effort e > 0 the retailer's optimal orders are {eQ̲₀}, {eQ̲₁} or {eQ̲₀, eQ̲₁} as e <, >, = T/τ
-- statement:
--   Consider the retailer under a target rebate and returns: wholesale price $w < p$, rebate $u > 0$ per unit sold beyond the target $T \ge 0$, and return credit $b$ with $s \le b < w$. Demand is $e\xi$, where $\xi$ has a density that vanishes on $(-\infty,0)$ and is strictly positive on $[0,\infty)$, with finite mean. Let $\underline Q_0, \underline Q_1 > 0$ be given by
--   $$\Phi(\underline Q_0) = \frac{p - w}{p - b}, \qquad \Phi(\underline Q_1) = \frac{p + u - w}{p + u - b},$$
--   and let $\tau \in [\underline Q_0, \underline Q_1]$ satisfy $r_b(\underline Q_0 \mid \tau) = r_b(\underline Q_1 \mid \tau)$, where $r_b(Q \mid T) = -wQ + pE\min(Q,\xi) + bE(Q-\xi)^+ + uE(\min(Q,\xi) - T)^+$ is the quantity-only profit with $b$ in place of $s$.
--
--   Fix an effort level $e \ge 0$ and consider $Q \mapsto R(Q, e \mid T)$ over $Q \ge 0$. Its set of maximizers is
--   $$Q^* = \begin{cases} \{e\underline Q_0\} & \text{if } e < T/\tau, \\ \{e\underline Q_1\} & \text{if } e > T/\tau, \\ \{e\underline Q_0,\ e\underline Q_1\} & \text{if } e = T/\tau. \end{cases}$$
--   In particular, for a linear rebate ($T = 0$) the optimal order is $e\underline Q_1$ for every $e > 0$.
--
--   This reduces the retailer's two-dimensional problem to a choice of effort alone, and is the step that the proof of Proposition 2 uses (with $b = s$) to pin down the retailer's order given her effort.
--
--   **Formalization Note** The paper writes "for any given $e$"; the statement covers every $e \ge 0$ (at $e = 0$ demand is $0$ and the unique optimal order is $0 = e\underline Q_0$, consistent with the case split). The quantiles $\Phi^{-1}(\cdot)$ and the threshold $\tau$ are given by their defining equations; that $\tau$ exists, is unique and lies in the open interval is the analogue of Lemma 1(a) and is not part of this statement. The wholesale price, unit cost and salvage value enter only through $w < p$ and $s \le b < w$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1000, §4.2 (Q̲₀, Q₂) and §4.3, Lemma 2; p. 995, §3.2 (τ₀); proof in the Appendix, p. 1005

import Mathlib
import Definitions.Def_ChannelRebate_NoCoord_Setting

open MeasureTheory ProbabilityTheory

namespace ChannelRebate.NoCoord

theorem lemma2_optimal_order_given_effort (p s w u b T : ℝ) (hwp : w < p) (hu : 0 < u)
    (hsb : s ≤ b) (hbw : b < w) (hT : 0 ≤ T)
    (D : Demand) (V : EffortCost)
    (Q0 Q1 τ : ℝ) (hQ0_pos : 0 < Q0) (hQ0 : Phi D Q0 = (p - w) / (p - b))
    (hQ1_pos : 0 < Q1) (hQ1 : Phi D Q1 = (p + u - w) / (p + u - b))
    (hτ : τ ∈ Set.Icc Q0 Q1)
    (hfτ : quantityProfit p w u b D τ Q0 = quantityProfit p w u b D τ Q1)
    (e : ℝ) (he : 0 ≤ e) :
    (e < T / τ →
      optimalOrders (fun Q => retailerProfit p w u b T D V Q e) = {e * Q0}) ∧
    (T / τ < e →
      optimalOrders (fun Q => retailerProfit p w u b T D V Q e) = {e * Q1}) ∧
    (e = T / τ →
      optimalOrders (fun Q => retailerProfit p w u b T D V Q e) = {e * Q0, e * Q1}) := by sorry

end ChannelRebate.NoCoord
