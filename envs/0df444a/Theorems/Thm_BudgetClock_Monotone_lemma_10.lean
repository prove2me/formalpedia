-- Prove2me | Theorems.Thm_BudgetClock_Monotone_lemma_10
-- name    : BudgetClock.Monotone.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:27.148147+00:00
-- url     : https://prove2.me/theorems/3a24d2a8-ffa2-4dbd-91b8-bd95f02075c4
-- title:
--   Lemma 10, p. 22 — if W̄₂ is not budget feasible, OPT ≤ 3.75 · v(W₃)
-- statement:
--   Let $v$ be a non-negative monotone submodular valuation, $c_i \ge 0$ the costs and $B > 0$ the budget, and run Iterative-Pruning, with final prices $p$. If $\overline W_2$ is not budget feasible, $\sum_{i \in \overline W_2} p_i > B$, then every set $O$ with $\sum_{i\in O} c_i \le B$ satisfies
--   $$v(O) \le 3.75\, v(W_3),$$
--   where $W_3 = W_2 \cup T$ is the second candidate of Maximize-Value.
--
--   This is the case of Theorem 1 in which the set built in the last phase, together with a possibly moved bidder $j^*$, exceeds the budget.
--
--   **Formalization Note** No hypothesis on the last phase $\hat t$ is made, as on the page: the paper's Lemma 9 appeals to this lemma at $\hat t = 2$ (the printed proof writes out only $\hat t \ge 3$; at $\hat t = 1$ the hypothesis cannot hold, since $\overline W_2 = S_1$ costs exactly $B$). $B > 0$ is added.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 22, Appendix A.3, Lemma 10

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism

namespace BudgetClock.Monotone

/-- Lemma 10, p. 22: if `W̄_2` is not budget feasible at the final prices, then
`OPT ≤ 3.75 · v(W_3)` (for every last phase `t̂`; the page's Lemma 9 uses it at `t̂ = 2`). -/
theorem lemma_10 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B)
    (hinf : B < listCost (finalPrices v c B) (W2bar v c B)) :
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B → v O ≤ (15 / 4 : ℝ) * v (W3 v c B).toFinset := by sorry

end BudgetClock.Monotone
