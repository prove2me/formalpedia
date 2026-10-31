-- Prove2me | Theorems.Thm_CapacityGames_profit_decomposition
-- name    : CapacityGames.profit_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:44.368027+00:00
-- url     : https://prove2.me/theorems/63670eb1-2c69-42d9-a683-d36698f79bc1
-- title:
--   The supply chain profit is $\Pi_{\mathcal B}+\sum_i\pi_i$ and does not depend on the bids (3)
-- statement:
--   Consider a capacity game with suppliers $N$, revenue $V$, execution costs $C_i$ and capacity costs $E_i$. Let $\mathcal B=\{(P_i,R_i):i\in N\}$ be any set of bids and $(t,s)$ a buyer choice that is feasible for $\mathcal B$. Then the supply chain profit splits as the buyer's profit plus the suppliers' profits, and the bids cancel:
--   $$\Pi_{\mathcal C}(t,s)=\Pi_{\mathcal B}(t,s)+\sum_{i\in N}\pi_i(t,s)=\mathbb E\Big[V(D,s(D))-\sum_{i\in N}\big(C_i(s(D))+E_i(t)\big)\Big].$$
--
--   This is the identity behind every profit computation in the proof of Theorem 2: a supplier's profit is the supply chain profit minus what the buyer and the other suppliers keep.
--
--   **Formalization Note** $\Pi_{\mathcal C}$ is defined by the bid-free expression, so the statement is the equality with $\Pi_{\mathcal B}+\sum_i\pi_i$. Feasibility for $\mathcal B$ includes integrability of $V(\cdot,s(\cdot))$, $C_i(s(\cdot))$ and $P_i(s(\cdot))$.
--
--   Differences from the source:
--   - generalization: bids in the allowed sets $A_i$ → any bids; reason: the identity is algebraic and uses no property of the bids, so it specializes to allowed bids.
--   - reading: expectations taken without comment → integrability of $V(D,s(D))$, $C_i(s(D))$, $P_i(s(D))$ is part of feasibility; reason: the paper writes these expectations, which presupposes them; a Lean integral of a non-integrable function is 0.
--   - encoding: $N=\{1,\dots,n\}$ → a finite type $N$, vectors $N\to\mathbb R$, demand space a probability space; reason: Lean convention, same instances.
-- source:
--   Anderson–Chen–Shao, Capacity Games with Supply Function Competition, arXiv:1905.11084v1, §3, display (3), p.8

import Mathlib
import Definitions.Def_CapacityGames_SetFunction
import Definitions.Def_CapacityGames_Model

open MeasureTheory

namespace CapacityGames

/-- **The supply chain profit is the sum of all profits and does not depend on the bids**,
display (3), Anderson–Chen–Shao, *Capacity Games with Supply Function Competition*,
arXiv:1905.11084v1, §3, p.8: for every bid set `B` and every choice `(t, s)` feasible for `B`,
`Π_C(t, s) = Π_B(t, s) + Σ_{i∈N} π_i(t, s)`, where `Π_C` is the bid-free expression
`E[V(D, s(D)) − Σ_{i∈N} (C_i(s(D)) + E_i(t))]`.

**Formalization Note.** Feasibility for `B` includes integrability of `V(·, s(·))`,
`C_i(s(·))` and `P_i(s(·))`; the identity is false for Lean's integral without it. -/
theorem profit_decomposition {N Ω : Type*} [Fintype N] [MeasurableSpace Ω]
    (G : CapacityGame N Ω) (hG : G.IsValid) (B : N → Bid N) (p : Choice N Ω)
    (hp : BidFeasible G B p) :
    scProfit G p = buyerProfit G B p + ∑ i, supplierProfit G B i p := by sorry

end CapacityGames
