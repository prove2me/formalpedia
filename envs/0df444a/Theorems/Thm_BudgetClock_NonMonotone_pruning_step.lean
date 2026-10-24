-- Prove2me | Theorems.Thm_BudgetClock_NonMonotone_pruning_step
-- name    : BudgetClock.NonMonotone.pruning_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:29.364243+00:00
-- url     : https://prove2.me/theorems/b44d4bf8-e6df-4519-8d4d-2bab862003c2
-- title:
--   Pruning step, proof of Theorem 5, p. 14 — v(S) is at least half of every candidate's value
-- statement:
--   Let $v : 2^N \to \mathbb{R}_{\ge 0}$ be a non-negative submodular valuation, let $c_i \ge 0$ be the bidders' costs and $B > 0$ the budget, and let $\mathrm{USM}$ be any 2-approximate unconstrained submodular maximizer as in Lemma 7. Let $S$ be the set returned by Simultaneous-Iterative-Pruning (Mechanism 3) and $\hat t$ its last phase. Then
--
--   $$v(S) \ge \frac12 \max_{S' \in \{S^1_{\hat t-1},\, S^2_{\hat t-1},\, T^1_{\hat t},\, T^2_{\hat t},\, T^1_{\hat t-1},\, T^2_{\hat t-1}\}} v(S').$$
--
--   If line 14 removes no bidder, $S$ is the best candidate. Otherwise the inequality bounds the value lost by removing the last bidder. Combined with Lemma 7 it gives $v(S) \ge OPT/64$.
--
--   **Formalization Note**
--   1. The maximum is written as $v(S') / 2 \le v(S)$ for each of the six candidates $S'$.
--   2. The statement covers both cases of the paper's proof (a candidate from phase 1, where no bidder is removed, and $j > 1$) and every $\hat t$.
--   3. $B > 0$ is added (the paper says only "a budget $B$").
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 14, proof of Theorem 5 (the case j > 1 and the display before 'where the second inequality')

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_NonMonotone_Mechanism

namespace BudgetClock.NonMonotone

/-- Proof of Theorem 5, p. 14 (the pruning step): the returned set `S` has value at least half
the value of each of the six candidates, i.e. `v(S) ≥ ½ max_{S′} v(S′)`, whether or not line 14
removed a bidder. -/
theorem pruning_step {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (usm : Finset (Fin n) → Finset (Fin n))
    (husm : ∀ X, usm X ⊆ X ∧ ∀ Y ⊆ X, v Y ≤ 2 * v (usm X)) :
    ∀ L ∈ candidates usm (finalState v c B),
      v L.toFinset / 2 ≤ v (simultaneousIterativePruning v c B usm).1 := by sorry

end BudgetClock.NonMonotone
