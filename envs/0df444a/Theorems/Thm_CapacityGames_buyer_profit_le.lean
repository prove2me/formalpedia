-- Prove2me | Theorems.Thm_CapacityGames_buyer_profit_le
-- name    : CapacityGames.buyer_profit_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:37.770547+00:00
-- url     : https://prove2.me/theorems/eca16049-bce4-40a3-a8f4-3d23fe6bfe1c
-- title:
--   (A-2): under the bids $\bar{\mathcal B}$, $\Pi_{\bar{\mathcal B}}(t,s)\le\Pi^*_{\mathcal C}(N)-\sum_j(\Pi^*_{\mathcal C}(N)-\Pi^*_{\mathcal C}(N\setminus\{j\}))$
-- statement:
--   Consider a capacity game in which $\Pi^*_{\mathcal C}$ satisfies the submodularity inequalities (6). Let $\{\Delta_j\ge0\}$ be a family consistent with the costs (8), and let $\bar{\mathcal B}$ be the bids of Theorem 2: $\bar P_i=C_i$ for all $i$, $\bar R_i(t)=E_i(t)+\Pi^*_{\mathcal C}(N)-\Pi^*_{\mathcal C}(N\setminus\{i\})-\Delta_i(t)$ for $t_i>0$ and $0$ for $t_i=0$ when $i\in N^*(\mathcal C)$, and $\bar R_i=E_i$ otherwise. Then every choice $(t,s)$ feasible for $\bar{\mathcal B}$ gives the buyer at most
--   $$\Pi_{\bar{\mathcal B}}(t,s)\le\Pi^*_{\mathcal C}(N)-\sum_{j\in N}\big(\Pi^*_{\mathcal C}(N)-\Pi^*_{\mathcal C}(N\setminus\{j\})\big).\quad(\text{A-2})$$
--
--   The proof of Theorem 2 then shows that the supply chain optimal choice attains this bound, so it is the buyer's optimal profit under $\bar{\mathcal B}$.
--
--   Differences from the source:
--   - generalization: assumptions (a)–(c), p.8 (made "to ensure that the maxima exist and are attained") → not assumed; reason: consistency (8) with $\Delta\ge0$ already asserts that every maximum $\Pi^*_{\mathcal C}(S)$ is attained, which is all (a)–(c) are used for.
--   - generalization: proved under Assumptions 1–3 inside the proof of Theorem 2 → without Assumptions 1 and 2; reason: (A-2) does not use them.
--   - generalization: $\{\Delta_i\ge0: i\in N^*(\mathcal C)\}$ consistent → $\Delta_i\ge0$ on $\mathbf T$ for every $i\in N$, consistent; reason: consistency (p.11) is defined for families indexed by $N$; the paper's family extended by $0$ is one, and $\bar{\mathcal B}$ reads $\Delta$ only on $N^*(\mathcal C)$.
--   - generalization: (8) attained at $t^*_S$ → attained at some supply chain optimal choice for $S$; reason: the weaker hypothesis gives the stronger statement and is all the proof uses.
--   - reading: expectations taken without comment → integrability of $V(D,s(D))$, $C_i(s(D))$, $P_i(s(D))$ is part of feasibility; reason: the paper writes these expectations, which presupposes them.
--   - encoding: $N=\{1,\dots,n\}$, $I(t)=\{i:t_i>0\}$, case $t_i>0$ in $\bar R_i$ → a finite type $N$, $I(t)=\{i:t_i\ne0\}$, case $t_i\ne0$, $\Pi^*_{\mathcal C}$ as a supremum; reason: equal on $\mathbf T$ because $T_i\subseteq\mathbb R_+$; Lean convention.
-- source:
--   Anderson–Chen–Shao, Capacity Games with Supply Function Competition, arXiv:1905.11084v1, App. A.5, (A-2), p.28

import Mathlib
import Definitions.Def_CapacityGames_SetFunction
import Definitions.Def_CapacityGames_Model

open MeasureTheory

namespace CapacityGames

/-- **Upper bound on the buyer's profit under the equilibrium bids**, display (A-2),
arXiv:1905.11084v1, App. A.5, p.28: under submodularity (6), for a family `Δ ≥ 0` consistent
with the costs, every choice `(t, s)` feasible for the bids `B̄` of Theorem 2 has
`Π_B̄(t, s) ≤ Π*_C(N) − Σ_{j∈N} (Π*_C(N) − Π*_C(N ∖ {j}))`.

The semicontinuity assumptions (a)–(c), p.8, are not imposed: consistency (8) with `Δ ≥ 0`
already says that every maximum `Π*_C(S)` is attained. -/
theorem buyer_profit_le {N Ω : Type*} [Fintype N] [DecidableEq N] [MeasurableSpace Ω]
    (G : CapacityGame N Ω) (hG : G.IsValid)
    (hsub : LocalSubmodular (scOptValue G))
    (Δ : N → (N → ℝ) → ℝ) (hΔ : ∀ i, ∀ t ∈ G.capSet, 0 ≤ Δ i t) (hcons : Consistent G Δ)
    (p : Choice N Ω) (hp : BidFeasible G (barBids G Δ) p) :
    buyerProfit G (barBids G Δ) p ≤
      scOptValue G Finset.univ -
        ∑ j, (scOptValue G Finset.univ - scOptValue G (Finset.univ.erase j)) := by sorry

end CapacityGames
