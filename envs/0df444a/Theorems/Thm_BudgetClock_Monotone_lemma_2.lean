-- Prove2me | Theorems.Thm_BudgetClock_Monotone_lemma_2
-- name    : BudgetClock.Monotone.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:18.245954+00:00
-- url     : https://prove2.me/theorems/e9a85aef-ea63-4ea5-a932-bf6bce108edc
-- title:
--   Lemma 2, p. 7 — v(R | W₁ ∪ W̄₂) ≤ (3/2 − 1/2^{t̂−2}) · OP̃T_t̂ (for t̂ ≥ 3)
-- statement:
--   Let $v$ be a non-negative monotone submodular valuation, $c_i \ge 0$ the costs and $B > 0$ the budget, and run Iterative-Pruning. Let $\hat t$ be its last phase, $\widetilde{\mathrm{OPT}}_{\hat t}$ the target of that phase, and $W_1$, $\overline W_2$ the sets after pruning. Assume $\hat t \ge 3$. Then every set $Q \subseteq N \setminus (W_1 \cup \overline W_2)$ with $\sum_{i\in Q} c_i \le B$ satisfies
--   $$v(Q \mid W_1 \cup \overline W_2) \le \Bigl(\frac32 - \frac1{2^{\hat t-2}}\Bigr)\cdot \widetilde{\mathrm{OPT}}_{\hat t};$$
--   in particular this holds for the maximizer $R$ of the paper.
--
--   The lemma bounds the part of the optimum lost through rejected bidders, the second term of the benchmark.
--
--   **Formalization Note** The hypothesis $\hat t \ge 3$ is added. The lemma is false for $\hat t = 2$: for the additive valuation with weights $(1, 0.99, 0.99)$ and costs $(0, B/2, B/2)$, bidders 2 and 3 reject $0.99\,B/2$ in phase 2, so $\hat t = 2$, $W_1 = \{1\}$, $\overline W_2 = \emptyset$, and $R = \{2,3\}$ has $v(R \mid W_1) = 1.98 > \tfrac12\widetilde{\mathrm{OPT}}_2 = 1$. The proof of Theorem 1 uses the lemma only when $\hat t \ge 3$; the case $\hat t \le 2$ is Lemma 9. $B > 0$ is added.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 7, Lemma 2

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism

namespace BudgetClock.Monotone

/-- Lemma 2, p. 7, for a last phase `t̂ ≥ 3`: every budget-feasible (at true costs) set `Q` of bidders
outside `W_1 ∪ W̄_2` has `v(Q | W_1 ∪ W̄_2) ≤ (3/2 − 1/2^{t̂−2}) · OP̃T_t̂`; in particular so does the
maximizer `R`. -/
theorem lemma_2 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) (h3 : 3 ≤ lastPhase v c B) :
    ∀ Q : Finset (Fin n),
      Q ⊆ Finset.univ \ ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) →
      ∑ i ∈ Q, c i ≤ B →
      marg v Q ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) ≤
        (3 / 2 - 1 / (2 : ℝ) ^ (lastPhase v c B - 2)) * target v c B (lastPhase v c B) := by sorry

end BudgetClock.Monotone
