-- Prove2me | Theorems.Thm_BudgetClock_NonMonotone_lemma_7
-- name    : BudgetClock.NonMonotone.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:09.329528+00:00
-- url     : https://prove2.me/theorems/029671b3-3b07-41a3-98c0-e83eefea6766
-- title:
--   Lemma 7, p. 13 — the best of the six candidates of the last two phases has value at least OPT/32
-- statement:
--   Let $v : 2^N \to \mathbb{R}_{\ge 0}$ be a non-negative submodular valuation, let $c_i \ge 0$ be the bidders' costs and $B > 0$ the budget. Let $\mathrm{USM}$ be any map that sends each set $X \subseteq N$ to a subset $\mathrm{USM}(X) \subseteq X$ with
--
--   $$2\,v(\mathrm{USM}(X)) \ge v(Y) \quad \text{for every } Y \subseteq X,$$
--
--   that is, a 2-approximation for unconstrained submodular maximization. Run Simultaneous-Iterative-Pruning (Mechanism 3) with this subroutine, let $\hat t$ be its last phase and $T^k_j = \mathrm{USM}(S^k_j)$. Then for every set $O$ with $\sum_{i \in O} c_i \le B$,
--
--   $$\max_{S' \in \{S^1_{\hat t-1},\, S^2_{\hat t-1},\, T^1_{\hat t},\, T^2_{\hat t},\, T^1_{\hat t-1},\, T^2_{\hat t-1}\}} v(S') \ge \frac{v(O)}{32}.$$
--
--   In particular the best of the six candidates of line 12 has value at least $OPT/32$. Together with the pruning step this yields the 64-approximation of Theorem 5.
--
--   **Formalization Note**
--   1. The maximum is written as the existence of one of the six candidates with value at least $v(O)/32$.
--   2. The statement is for every budget-feasible $O$, in particular an optimal one. For $\hat t = 1$ the candidates $S^1_0, S^2_0$ are empty.
--   3. The subroutine is universally quantified, as the paper uses only its guarantee ("for example the algorithm of Buchbinder et al.").
--   4. $B > 0$ is added (the paper says only "a budget $B$").
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 13, Lemma 7 (proof on pp. 13–14, displays (6)–(9))

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_NonMonotone_Mechanism

namespace BudgetClock.NonMonotone

/-- Lemma 7, p. 13: for every budget-feasible set `O` (in particular an optimal one, of value
`OPT`), one of the six candidates `S¹_{t̂-1}, S²_{t̂-1}, T¹_{t̂}, T²_{t̂}, T¹_{t̂-1}, T²_{t̂-1}` has
value at least `v(O) / 32`, for every subroutine `usm` returning a subset of its input of value
at least half the best subset. -/
theorem lemma_7 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (usm : Finset (Fin n) → Finset (Fin n))
    (husm : ∀ X, usm X ⊆ X ∧ ∀ Y ⊆ X, v Y ≤ 2 * v (usm X))
    (O : Finset (Fin n)) (hO : ∑ i ∈ O, c i ≤ B) :
    ∃ L ∈ candidates usm (finalState v c B), v O / 32 ≤ v L.toFinset := by sorry

end BudgetClock.NonMonotone
