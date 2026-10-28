-- Prove2me | Theorems.Thm_BudgetClock_Monotone_lemma_11
-- name    : BudgetClock.Monotone.lemma_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:20.095986+00:00
-- url     : https://prove2.me/theorems/2dc10130-e5a7-41ed-b67f-f8d1f2c4cc60
-- title:
--   Lemma 11, p. 23 — Iterative-Pruning is budget feasible (W₁, W₂, W₃ and the output)
-- statement:
--   Let $v$ be a non-negative monotone submodular valuation, $c_i \ge 0$ the costs and $B > 0$ the budget, and run Iterative-Pruning with final prices $p$. Then each of the sets $W_1$, $W_2$, $W_3$ of Maximize-Value costs at most $B$ at the final prices,
--   $$\sum_{i \in W_1} p_i \le B, \qquad \sum_{i \in W_2} p_i \le B, \qquad \sum_{i \in W_3} p_i \le B,$$
--   and so does the output $W$: $\sum_{i \in W} p_i \le B$. That is, Iterative-Pruning is a budget-feasible mechanism.
--
--   **Formalization Note** The payments are the final clock prices, not the costs. The section's standing assumptions (monotone, submodular, $v \ge 0$, $c \ge 0$) are kept as hypotheses although the argument does not use all of them; $B > 0$ is added.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 23, Appendix A.4, Lemma 11

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism

namespace BudgetClock.Monotone

/-- Lemma 11, p. 23: Iterative-Pruning is budget feasible: `W_1`, `W_2` and `W_3` each cost at most `B`
at the final prices, and so does the output `W`. -/
theorem lemma_11 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) :
    listCost (finalPrices v c B) (W1 v c B) ≤ B ∧
    listCost (finalPrices v c B) (W2 v c B) ≤ B ∧
    listCost (finalPrices v c B) (W3 v c B) ≤ B ∧
    ∑ i ∈ (iterativePruning v c B).1, (iterativePruning v c B).2 i ≤ B := by sorry

end BudgetClock.Monotone
