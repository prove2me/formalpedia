-- Prove2me | Theorems.Thm_CapacityGames_theorem_2
-- name    : CapacityGames.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:48.981984+00:00
-- url     : https://prove2.me/theorems/d8edb28f-9289-41a5-8089-aef1830d21e7
-- title:
--   Theorem 2 (Nash Equilibrium): under submodularity, at-cost bids with marginal-contribution margins are a supply-chain-optimal Nash equilibrium
-- statement:
--   Consider a general capacity game: finitely many suppliers $N$, compact capacity sets $T_i\subseteq\mathbb R_+$ containing $0$, a random demand $D$, execution sets $X(t)$, revenue $V(D,s)$, and supplier costs $E_i(t)$, $C_i(s)$ that vanish when supplier $i$ is not used. Let $\Pi^*_{\mathcal C}(S)$ be the optimal supply chain profit when only the suppliers in $S$ may be used, and $N^*(\mathcal C)=\{i:\Pi^*_{\mathcal C}(N)>\Pi^*_{\mathcal C}(N\setminus\{i\})\}$. Assume
--
--   1. Assumption 1 (Tie-Breaking Rule): among several optimal choices the buyer picks one with the largest supply chain profit;
--   2. Assumption 2 (Uniqueness of Support): all supply chain optimal choices use the same set of suppliers;
--   3. Assumption 3 (Submodularity): $\Pi^*_{\mathcal C}(S)-\Pi^*_{\mathcal C}(S\setminus\{i\})\le\Pi^*_{\mathcal C}(S\setminus\{j\})-\Pi^*_{\mathcal C}(S\setminus\{i,j\})$ for all $S\subseteq N$ and $i\ne j$ in $S$;
--
--   and let $\{\Delta_i\ge0\}$ be any family of functions consistent with the costs (8). Define the bids
--   $$\bar{\mathcal B}=\{(C_i(\cdot),\bar R_i(\cdot)):i\in N^*(\mathcal C)\}\cup\{(C_i(\cdot),E_i(\cdot)):i\notin N^*(\mathcal C)\},$$
--   $$\bar R_i(t)=\begin{cases}E_i(t)+\Pi^*_{\mathcal C}(N)-\Pi^*_{\mathcal C}(N\setminus\{i\})-\Delta_i(t),& t_i>0,\\ 0,& t_i=0.\end{cases}$$
--   Then:
--
--   1. $\bar{\mathcal B}$ is a Nash equilibrium: the buyer has an optimal choice, and no supplier can increase its profit by unilaterally changing its bid;
--   2. every choice the buyer makes under $\bar{\mathcal B}$ is supply chain optimal, $\Pi_{\mathcal C}(t,s)=\Pi^*_{\mathcal C}(N)$;
--   3. the buyer's profit is $\Pi^*_{\mathcal C}(N)-\sum_{i\in N}\big(\Pi^*_{\mathcal C}(N)-\Pi^*_{\mathcal C}(N\setminus\{i\})\big)$;
--   4. every supplier $i\in N$ earns $\Pi^*_{\mathcal C}(N)-\Pi^*_{\mathcal C}(N\setminus\{i\})$, its marginal contribution to the supply chain.
--
--   The equilibrium profit split is the Vickrey–Clarke–Groves split, obtained here as an equilibrium of a pay-as-bid game, and the supply chain is coordinated in equilibrium.
--
--   **Formalization Note** A Nash equilibrium is a bid set of allowed bids (vanishing at zero capacity, resp. execution) such that the buyer has a tie-broken optimal choice, and for every supplier $i$, every allowed bid $b$ of $i$, every buyer choice under $\bar{\mathcal B}$ and every buyer choice under the deviated bids, supplier $i$'s profit after deviating is at most its profit before. Clauses 2–4 are stated for every tie-broken buyer choice. No semicontinuity assumption is imposed: consistency (8) with $\Delta\ge0$ already says that every maximum $\Pi^*_{\mathcal C}(S)$ is attained.
--
--   Differences from the source:
--   - generalization: assumptions (a)–(c), p.8 (made "to ensure that the maxima exist and are attained") → not assumed; reason: consistency (8) with $\Delta\ge0$ already asserts that every maximum $\Pi^*_{\mathcal C}(S)$ is attained, which is all (a)–(c) are used for.
--   - generalization: deviations within $A_i$ (lower semicontinuous bids vanishing at zero) → all bids vanishing at zero; reason: a larger deviation set makes the equilibrium claim stronger.
--   - generalization: (8) "attained at $t^*_S$" → attained at some supply chain optimal choice for $S$; reason: the weaker hypothesis gives the stronger theorem.
--   - generalization: $\{\Delta_i\ge0: i\in N^*(\mathcal C)\}$ consistent → $\Delta_i\ge0$ on $\mathbf T$ for every $i\in N$, consistent; reason: consistency (p.11) is defined for families indexed by $N$; the paper's family extended by $0$ is one, and $\bar{\mathcal B}$ reads $\Delta$ only on $N^*(\mathcal C)$.
--   - reading: expectations taken without comment → integrability of $V(D,s(D))$, $C_i(s(D))$, $P_i(s(D))$ is part of feasibility; reason: the paper writes these expectations, which presupposes them; a Lean integral of a non-integrable function is 0.
--   - reading: "Nash equilibrium" (not defined in the paper) → allowed bids, a tie-broken buyer choice exists, and no unilateral deviation to an allowed bid raises the deviator's profit for any buyer choices before and after; reason: §4 describes suppliers as Stackelberg leaders facing the buyer's tie-broken response (Assumption 1), and the proof (pp.29–31) compares the deviator's profit at an arbitrary optimal buyer choice. The deviation clause is vacuous for a deviation under which the buyer has no tie-broken optimal choice; the paper's (a)–(c) exclude such deviations, and `deviation_profit_le` bounds every deviation without that restriction.
--   - generalization: "the buyer makes a supply chain optimal choice", "the buyer makes profit …", "supplier $i$ makes profit …" (for the buyer's choice) → stated for every tie-broken buyer choice under $\bar{\mathcal B}$ and every $i\in N$; reason: holding for every tie-broken choice specializes to the one the buyer makes.
--   - encoding: $N=\{1,\dots,n\}$, $I(t)=\{i:t_i>0\}$, case $t_i>0$ in $\bar R_i$, $\Pi^*_{\mathcal C}$ as $\max$ → a finite type $N$, $I(t)=\{i:t_i\ne0\}$, case $t_i\ne0$, $\Pi^*_{\mathcal C}$ as a supremum; reason: equal on $\mathbf T$ because $T_i\subseteq\mathbb R_+$; the supremum is attained by hypothesis.
-- source:
--   Anderson–Chen–Shao, Capacity Games with Supply Function Competition, arXiv:1905.11084v1, §4, Theorem 2, p.11 (model §3, pp.6–8; Assumptions 1–3, pp.9–10; consistency (8), p.11; proof App. A.5, pp.27–31)

import Mathlib
import Definitions.Def_CapacityGames_SetFunction
import Definitions.Def_CapacityGames_Model

open MeasureTheory

namespace CapacityGames

/-- **Theorem 2 (Nash Equilibrium)**, Anderson–Chen–Shao, *Capacity Games with Supply Function
Competition*, arXiv:1905.11084v1, §4, p.11 (proof App. A.5, pp.27–31). "If Assumptions 1–3 hold,
then the set of bids `B̄ = {(C_i(·), R̄_i(·)) : i ∈ N*(𝒞)} ∪ {(C_i(·), E_i(·)) : i ∉ N*(𝒞)}` is a
Nash equilibrium, where `R̄_i(t) = E_i(t) + Π*_C(N) − Π*_C(N∖{i}) − Δ_i(t)` if `t_i > 0`, `0` if
`t_i = 0`, and `{Δ_i(·) ≥ 0}` is any set of functions consistent with the costs. In equilibrium,
the buyer makes a supply chain optimal choice `(t*_N, s*_N)`. The buyer makes profit
`Π*_C(N) − Σ_{i=1}^n (Π*_C(N) − Π*_C(N ∖ {i}))` and supplier `i` makes profit
`Π*_C(N) − Π*_C(N ∖ {i})`."

Hypotheses: the standing conditions of §3 (`hG`); Assumption 2 (`huniq`); Assumption 3 in the
form (6) (`hsub`); a family `Δ ≥ 0` on `𝐓` consistent with the costs (8). Assumption 1 is built
into `BuyerChoice`. The paper's semicontinuity assumptions (a)–(c), p.8, are not imposed: (8)
with `Δ ≥ 0` already says that every maximum (4) is attained.

Conclusions: `B̄` is a Nash equilibrium, and **every** tie-broken buyer choice under `B̄` is
supply chain optimal and yields the stated buyer and supplier profits (for every `i ∈ N`).

**Formalization Note.** `N` is a finite type; `I(t)` is `{i : t_i ≠ 0}`; `Π*_C` is an `sSup`
(attained, by (8)); integrability of the integrands is part of feasibility; "Nash
equilibrium" is `IsNashEquilibrium` (allowed bids are all bids vanishing at zero capacity or
execution); `Δ` is indexed by all of `N`. -/
theorem theorem_2 {N Ω : Type*} [Fintype N] [DecidableEq N] [MeasurableSpace Ω]
    (G : CapacityGame N Ω) (hG : G.IsValid)
    (huniq : UniqueSupport G)
    (hsub : LocalSubmodular (scOptValue G))
    (Δ : N → (N → ℝ) → ℝ) (hΔ : ∀ i, ∀ t ∈ G.capSet, 0 ≤ Δ i t) (hcons : Consistent G Δ) :
    IsNashEquilibrium G (barBids G Δ) ∧
      (∀ p ∈ BuyerChoice G (barBids G Δ), scProfit G p = scOptValue G Finset.univ) ∧
      (∀ p ∈ BuyerChoice G (barBids G Δ),
        buyerProfit G (barBids G Δ) p =
          scOptValue G Finset.univ -
            ∑ i, (scOptValue G Finset.univ - scOptValue G (Finset.univ.erase i))) ∧
      (∀ p ∈ BuyerChoice G (barBids G Δ), ∀ i,
        supplierProfit G (barBids G Δ) i p =
          scOptValue G Finset.univ - scOptValue G (Finset.univ.erase i)) := by sorry

end CapacityGames
