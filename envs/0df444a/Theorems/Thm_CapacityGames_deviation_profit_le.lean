-- Prove2me | Theorems.Thm_CapacityGames_deviation_profit_le
-- name    : CapacityGames.deviation_profit_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:52.650804+00:00
-- url     : https://prove2.me/theorems/afc9e9f8-407c-42e6-860e-e109bb263b98
-- title:
--   No unilateral deviation pays: a deviating supplier earns at most $\Pi^*_{\mathcal C}(N)-\Pi^*_{\mathcal C}(N\setminus\{i\})$ (p.30)
-- statement:
--   Consider a capacity game in which $\Pi^*_{\mathcal C}$ satisfies the submodularity inequalities (6). Let $\{\Delta_j\ge0\}$ be consistent with the costs (8) and let $\bar{\mathcal B}$ be the bids of Theorem 2. Let supplier $i$ replace its bid by any offer $(\tilde P_i,\tilde R_i)$, the other suppliers keeping their bids in $\bar{\mathcal B}$; call the result $\tilde{\mathcal B}_i$. Let $(\tilde t,\tilde s)$ be any choice feasible for $\tilde{\mathcal B}_i$ that gives the buyer at least the outside option, $\Pi_{\tilde{\mathcal B}_i}(\tilde t,\tilde s)\ge\Pi^*_{\bar{\mathcal B}}(N\setminus\{i\})$. Then supplier $i$'s profit is
--   $$\mathbb E\big[\tilde P_i(\tilde s(D))+\tilde R_i(\tilde t)-\big(C_i(\tilde s(D))+E_i(\tilde t)\big)\big]\le\Pi^*_{\mathcal C}(N)-\Pi^*_{\mathcal C}(N\setminus\{i\}).$$
--
--   Every optimal choice of the buyer under $\tilde{\mathcal B}_i$ meets the outside-option condition when the offer vanishes at $t_i=0$, $s_i=0$, so no unilateral deviation earns supplier $i$ more than its equilibrium margin.
--
--   Differences from the source:
--   - generalization: suppliers $i\in N^*(\mathcal C)$ (p.30; $i\notin N^*(\mathcal C)$ by a separate argument on p.31) → every supplier $i\in N$; reason: the bound holds for all $i$ and specializes to both cases.
--   - generalization: an optimal choice $(\tilde t,\tilde s)$ of the buyer under $\tilde{\mathcal B}_i$ → any feasible choice with buyer profit at least $\Pi^*_{\bar{\mathcal B}}(N\setminus\{i\})$; reason: the paper's argument uses optimality only through this bound (p.30), which every optimal choice satisfies.
--   - generalization: offers in the allowed set $A_i$ → any offer; reason: the bound uses no property of the offer once the outside-option condition is assumed.
--   - generalization: assumptions (a)–(c), p.8 (made "to ensure that the maxima exist and are attained") → not assumed; reason: consistency (8) with $\Delta\ge0$ already asserts that every maximum $\Pi^*_{\mathcal C}(S)$ is attained, which is all (a)–(c) are used for.
--   - generalization: proved under Assumptions 1–3 → without Assumptions 1 and 2; reason: the argument does not use them.
--   - generalization: $\{\Delta_i\ge0: i\in N^*(\mathcal C)\}$ consistent, (8) attained at $t^*_S$ → $\Delta_i\ge0$ on $\mathbf T$ for every $i\in N$, consistent, attained at some supply chain optimal choice for $S$; reason: the paper's family extended by $0$ is one; the weaker hypothesis gives the stronger statement.
--   - reading: expectations taken without comment → integrability of $V(D,s(D))$, $C_i(s(D))$, $P_i(s(D))$ is part of feasibility; reason: the paper writes these expectations, which presupposes them.
--   - encoding: $N=\{1,\dots,n\}$, $\Pi^*$ as $\max$ → a finite type $N$, $\Pi^*$ as a supremum; reason: Lean convention; under the hypotheses the suprema are attained.
-- source:
--   Anderson–Chen–Shao, Capacity Games with Supply Function Competition, arXiv:1905.11084v1, App. A.5, p.30 (last display) and p.31

import Mathlib
import Definitions.Def_CapacityGames_SetFunction
import Definitions.Def_CapacityGames_Model

open MeasureTheory

namespace CapacityGames

/-- **No unilateral deviation pays**, arXiv:1905.11084v1, App. A.5, p.30 (last display): under
submodularity (6), for a family `Δ ≥ 0` consistent with the costs and the bids `B̄` of
Theorem 2, let supplier `i` replace its bid by any bid `b`, giving `B̃ = B̄[i ↦ b]`. Every choice
`(t̃, s̃)` feasible for `B̃` that gives the buyer at least the outside option `Π*_B̄(N ∖ {i})`
gives supplier `i` the profit
`E[P̃_i(s̃(D)) + R̃_i(t̃) − (C_i(s̃(D)) + E_i(t̃))] ≤ Π*_C(N) − Π*_C(N ∖ {i})`.

**Formalization Note.** The paper proves this for `i ∈ N*(𝒞)` and an optimal choice of the buyer
under `B̃` (which gives the buyer at least `Π*_B̄(N ∖ {i})`, p.30). The statement covers every
supplier, every bid `b`, and every choice meeting the outside-option bound.

The semicontinuity assumptions (a)–(c), p.8, are not imposed: consistency (8) with `Δ ≥ 0`
already says that every maximum `Π*_C(S)` is attained. -/
theorem deviation_profit_le {N Ω : Type*} [Fintype N] [DecidableEq N] [MeasurableSpace Ω]
    (G : CapacityGame N Ω) (hG : G.IsValid)
    (hsub : LocalSubmodular (scOptValue G))
    (Δ : N → (N → ℝ) → ℝ) (hΔ : ∀ i, ∀ t ∈ G.capSet, 0 ≤ Δ i t) (hcons : Consistent G Δ)
    (i : N) (b : Bid N) (q : Choice N Ω)
    (hq : BidFeasible G (Function.update (barBids G Δ) i b) q)
    (hout : buyerOptValue G (barBids G Δ) (Finset.univ.erase i) ≤
      buyerProfit G (Function.update (barBids G Δ) i b) q) :
    supplierProfit G (Function.update (barBids G Δ) i b) i q ≤
      scOptValue G Finset.univ - scOptValue G (Finset.univ.erase i) := by sorry

end CapacityGames
