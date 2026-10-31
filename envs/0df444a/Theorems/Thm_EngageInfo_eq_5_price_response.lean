-- Prove2me | Theorems.Thm_EngageInfo_eq_5_price_response
-- name    : EngageInfo.eq_5_price_response
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:42.725029+00:00
-- url     : https://prove2.me/theorems/6881dcd3-4429-4a90-87cc-c97f7d61070e
-- title:
--   (5) — the seller's price response: cut to $\theta_L+e$ iff $\alpha<\alpha_e$
-- statement:
--   Let $\alpha\in[0,1]$ be the belief and $e\in\{0,\bar e\}$ the observed engagement. A price $p$ maximizes the seller's expected profit $S(\alpha,e,\cdot)$ over all real prices if and only if
--
--   $$p=\begin{cases}\theta_L+e, & \alpha<\alpha_e,\\ \theta_H+e, & \alpha>\alpha_e,\\ \theta_L+e\ \text{or}\ \theta_H+e, & \alpha=\alpha_e,\end{cases}\qquad \alpha_e=\frac{\theta_L+e-c}{\theta_H+e-c},$$
--
--   and the maximal expected profit is $\max\{\theta_L+e-c,\ \alpha(\theta_H+e-c)\}$.
--
--   So the seller sells in both states at the low price below the threshold $\alpha_e$ and only in state $H$ at the high price above it. Lemma 1 and the payoff (6) are built on this response.
--
--   Differences from the source:
--   - reading: "the seller prefers to cut the price from p = θH + e to p = θL + e if and only if α < αe" → the full set of profit-maximizing prices over ℝ and the maximal profit max{θL + e − c, α(θH + e − c)}; reason: the sentence compares the two candidate prices; the Lean states the best response it describes, which Lemma 1 and (6) use
--   - reading: the customer purchases in state ω (rule left implicit) → the customer buys iff θ_ω + e − p ≥ 0, i.e. also at indifference; reason: without purchase at indifference the seller has no best price and no SPE exists
--   - encoding: e ∈ {0, ē}, belief α → e = effort M b for b : Bool, α ∈ [0,1]; reason: relabelling; beliefs are probabilities
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, §3.1, (5), p.9

import Mathlib
import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_subgame

namespace EngageInfo

/-- **The seller's price response and the threshold α_e of (5).**
Guo, *Designing Information to Engage Customers*, Management Science (2025), §3.1, p.9, (5):
"Similar to the benchmark, the seller prefers to cut the price from p = θH + e to p = θL + e if and
only if α < αe, where the threshold is αe ≡ (θL + e − c)/(θH + e − c)."

For a belief `α ∈ [0, 1]` and an engagement level `e ∈ {0, ē}`, a price `p` maximizes the seller's
expected profit `S(α, e, ·)` over all real prices iff `p = θ_L + e` when `α < α_e`, `p = θ_H + e` when
`α > α_e`, and `p ∈ {θ_L + e, θ_H + e}` when `α = α_e`; the maximal profit is
`max{θ_L + e − c, α(θ_H + e − c)}`.

**Formalization Note** Engagement is `b : Bool` with `e = effort M b`. Prices range over all of `ℝ`.
The customer buys at indifference. -/
theorem eq_5_price_response (M : Params) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (b : Bool) :
    (∀ p : ℝ, (∀ p' : ℝ, sellerProfit M α (effort M b) p' ≤ sellerProfit M α (effort M b) p) ↔
      ((α < M.alpha (effort M b) ∧ p = M.θL + effort M b) ∨
        (M.alpha (effort M b) < α ∧ p = M.θH + effort M b) ∨
        (α = M.alpha (effort M b) ∧ (p = M.θL + effort M b ∨ p = M.θH + effort M b)))) ∧
    IsGreatest (Set.range (sellerProfit M α (effort M b)))
      (max (M.θL + effort M b - M.c) (α * (M.θH + effort M b - M.c))) := by sorry

end EngageInfo
