-- Prove2me | Theorems.Thm_BudgetClock_NonMonotone_budget_feasible
-- name    : BudgetClock.NonMonotone.budget_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:16.441347+00:00
-- url     : https://prove2.me/theorems/a254254c-ecc1-4d44-a729-9e4182e2af67
-- title:
--   Budget feasibility of Mechanism 3, p. 12 — the returned set costs at most B at the returned prices
-- statement:
--   Let $v : 2^N \to \mathbb{R}_{\ge 0}$ be a non-negative submodular valuation, let $c_i \ge 0$ be the bidders' costs and $B > 0$ the budget, and let $\mathrm{USM}$ be any 2-approximate unconstrained submodular maximizer as in Lemma 7. If Simultaneous-Iterative-Pruning (Mechanism 3) returns the set $S$ with prices $p$, then
--
--   $$\sum_{i \in S} p_i \le B.$$
--
--   The paper states that the argument is the same as for Lemma 11, the budget feasibility of Iterative-Pruning. This is the first half of Theorem 5.
--
--   **Formalization Note**
--   1. Every bidder of $S$ is paid its final clock price $p_i$, the last price it accepted. The bidder of $S^2_1$, if it wins, has price $B$ and is never asked to accept anything, exactly as in the paper.
--   2. $B > 0$ is added (the paper says only "a budget $B$").
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 12, proof of Theorem 5 (budget feasibility, referring to Lemma 11, p. 23)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_NonMonotone_Mechanism

namespace BudgetClock.NonMonotone

/-- Budget feasibility of Mechanism 3, p. 12 ("identical to the proof of Lemma 11"): the returned
set `S` costs at most `B` at the returned prices. -/
theorem budget_feasible {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (usm : Finset (Fin n) → Finset (Fin n))
    (husm : ∀ X, usm X ⊆ X ∧ ∀ Y ⊆ X, v Y ≤ 2 * v (usm X)) :
    ∑ i ∈ (simultaneousIterativePruning v c B usm).1,
      (simultaneousIterativePruning v c B usm).2 i ≤ B := by sorry

end BudgetClock.NonMonotone
