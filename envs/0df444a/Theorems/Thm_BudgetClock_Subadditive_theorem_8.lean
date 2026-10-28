-- Prove2me | Theorems.Thm_BudgetClock_Subadditive_theorem_8
-- name    : BudgetClock.Subadditive.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:22.808502+00:00
-- url     : https://prove2.me/theorems/142e0cf9-b9bd-4188-af61-4d40f8b690a9
-- title:
--   Theorem 8, p. 15 — Mechanism 4 is budget feasible and an O(log n / log log n)-approximation for subadditive valuations
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Let $n \ge 3$ bidders have costs $c_i \ge 0$, let $B > 0$ be the budget, let $v : 2^N \to \mathbb{R}_{\ge 0}$ be a subadditive valuation, and let $\mathrm{alg}$ be any subroutine with the 2-approximation guarantee of Mechanism 4 (for each $t$ and pool $X$ it returns a subset of $X$ of at most $t$ bidders whose value is at least half that of every such subset). Run Mechanism 4 for at most $F$ phases, for any $F \ge n$, and let $S_{\mathrm{final}}$ and $p$ be its output. Then:
--   1. the payments are within the budget: $\sum_{i \in S_{\mathrm{final}}} p_i \le B$;
--   2. for every set $O$ of bidders that is feasible at true costs, $\sum_{i \in O} c_i \le B$,
--   $$v(O) \le C \cdot \frac{\log n}{\log\log n} \cdot v(S_{\mathrm{final}}).$$
--
--   Item 2 says that the auction obtains an $O(\log n / \log\log n)$-approximation to the optimal value, matching the best known (randomized) budget-feasible mechanism for subadditive valuations of Bei, Chen, Gravin and Lu, with a deterministic clock auction.
--
--   **Formalization Note**
--   1. The $O(\cdot)$ is a single constant $C$, chosen before $n$ and the instance. The threshold $n \ge 3$ makes $\log\log n > 0$; for $n \le 2$ the ratio $\log n/\log\log n$ is undefined or non-positive, and the asymptotic claim says nothing there. $\log$ is the natural logarithm; the base only changes $C$.
--   2. "OPT ≤ ρ·v(M(I))" is stated for every budget-feasible set $O$ instead of through a maximum.
--   3. $B > 0$ is added; §2 says only "a budget $B$".
--   4. The oracle is abstract: the theorem holds for every subroutine with the stated guarantee, the algorithm of Badanidiyuru, Dobzinski and Oren being one.
--   5. The paper does not bound the number of phases, and the loop need not stop on its own (zero-cost bidders never reject). The theorem is stated for the run cut after any $F \ge n$ phases, or stopped earlier by the loop condition; the proof only uses phases up to $n$.
--   6. "Polynomial-time", "deterministic" and "clock auction" are not part of the Lean statement: a Lean function is deterministic, running time is not modeled, and the clock property (prices $B/t$ only decrease, rejecting bidders leave for good) is built into the definition of Mechanism 4.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 15, Theorem 8 (proof pp. 15–16)

import Mathlib
import Definitions.Def_BudgetClock_Subadditive_Mechanism

namespace BudgetClock.Subadditive

theorem theorem_8 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 3 ≤ n →
      ∀ (v : Finset (Fin n) → ℝ), (∀ S, 0 ≤ v S) → IsSubadditive v →
      ∀ (c : Fin n → ℝ), (∀ i, 0 ≤ c i) →
      ∀ (B : ℝ), 0 < B →
      ∀ (alg : ℕ → Finset (Fin n) → Finset (Fin n)), IsTwoApproxOracle v alg →
      ∀ (F : ℕ), n ≤ F →
        (∑ i ∈ (mechanism4 v c B alg F).1, (mechanism4 v c B alg F).2 i ≤ B) ∧
        ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
          v O ≤ C * (Real.log n / Real.log (Real.log n)) *
            v (mechanism4 v c B alg F).1 := by sorry

end BudgetClock.Subadditive
