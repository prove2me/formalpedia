-- Prove2me | Theorems.Thm_BudgetClock_Monotone_benchmark_bound
-- name    : BudgetClock.Monotone.benchmark_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:19.547753+00:00
-- url     : https://prove2.me/theorems/b302293e-c793-416e-afd0-29549292b4e5
-- title:
--   §3, p. 7 — OPT ≤ v(W₁ ∪ W̄₂) + v(R | W₁ ∪ W̄₂)
-- statement:
--   Let $v$ be a non-negative monotone submodular valuation on the bidders $N$, let the costs be $c_i \ge 0$ and the budget $B > 0$, and let $W_1$ and $\overline W_2$ be the two sets of Iterative-Pruning after the pruning step (lines 11–17 of Mechanism 1). Let $\mathbf Q$ be the collection of sets $Q \subseteq N \setminus (W_1 \cup \overline W_2)$ with $\sum_{i \in Q} c_i \le B$, and let $R$ maximize $v(Q \mid W_1 \cup \overline W_2)$ over $\mathbf Q$. Then every set $O$ that is budget feasible at the true costs satisfies
--   $$v(O) \le v(W_1 \cup \overline W_2) + v(R \mid W_1 \cup \overline W_2),$$
--   in particular $\mathrm{OPT} \le v(W_1 \cup \overline W_2) + v(R \mid W_1 \cup \overline W_2)$.
--
--   The right-hand side is the benchmark against which the approximation factor of Theorem 1 is proved.
--
--   **Formalization Note** The argmax $R$ is not formed: the statement says that for every budget-feasible $O$ there is a $Q \in \mathbf Q$ with $v(O) \le v(W_1 \cup \overline W_2) + v(Q \mid W_1 \cup \overline W_2)$, which is the same as the bound with $R$. $B > 0$ is an added hypothesis (§2 only speaks of "a budget $B$").
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 7, §3 (benchmark, after Theorem 1); p. 9 / p. 19, proof of Theorem 1

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism

namespace BudgetClock.Monotone

/-- §3, p. 7: `OPT ≤ v(W_1 ∪ W̄_2) + v(R | W_1 ∪ W̄_2)`, where `R` maximizes `v(Q | W_1 ∪ W̄_2)` over
the budget-feasible (at true costs) sets `Q` of bidders outside `W_1 ∪ W̄_2`. Stated without the
argmax: every budget-feasible `O` is bounded through some such `Q`. -/
theorem benchmark_bound {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) :
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
      ∃ Q : Finset (Fin n),
        Q ⊆ Finset.univ \ ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) ∧
        ∑ i ∈ Q, c i ≤ B ∧
        v O ≤ v ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) +
          marg v Q ((W1 v c B).toFinset ∪ (W2bar v c B).toFinset) := by sorry

end BudgetClock.Monotone
