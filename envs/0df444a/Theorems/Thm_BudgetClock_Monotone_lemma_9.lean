-- Prove2me | Theorems.Thm_BudgetClock_Monotone_lemma_9
-- name    : BudgetClock.Monotone.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:38.838004+00:00
-- url     : https://prove2.me/theorems/c43f0734-4166-4791-9878-a64f0f497a1f
-- title:
--   Lemma 9, p. 21 — if t̂ ≤ 2, Iterative-Pruning is a 4-approximation
-- statement:
--   Let $v$ be a non-negative monotone submodular valuation, $c_i \ge 0$ the costs and $B > 0$ the budget, and run Iterative-Pruning, with output $W$. If the last phase satisfies $\hat t \le 2$, then every set $O$ with $\sum_{i\in O} c_i \le B$ satisfies
--   $$v(O) \le 4\, v(W),$$
--   i.e. $\mathrm{OPT} \le 4\,v(W)$.
--
--   Together with Lemma 10 and the main case of the proof, this covers the short runs in Theorem 1.
--
--   **Formalization Note** The statement has no hypothesis on $\overline W_2$. The paper's proof assumes $\overline W_2$ budget feasible and refers the other case to Appendix A.3, whose argument is written for $\hat t \ge 3$; the case $\hat t = 2$ with $\overline W_2$ not budget feasible is nevertheless true with factor $4$. $B > 0$ is added.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 21, Appendix A.2, Lemma 9

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism

namespace BudgetClock.Monotone

/-- Lemma 9, p. 21: if the last phase is `t̂ ≤ 2`, Iterative-Pruning returns a 4-approximation. -/
theorem lemma_9 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) (h2 : lastPhase v c B ≤ 2) :
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B → v O ≤ 4 * v (iterativePruning v c B).1 := by sorry

end BudgetClock.Monotone
