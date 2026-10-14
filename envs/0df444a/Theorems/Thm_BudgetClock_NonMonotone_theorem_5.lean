-- Prove2me | Theorems.Thm_BudgetClock_NonMonotone_theorem_5
-- name    : BudgetClock.NonMonotone.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:25.70501+00:00
-- url     : https://prove2.me/theorems/4c14c4ee-3c17-44b1-93b3-83b730c21240
-- title:
--   Theorem 5, p. 12 — Simultaneous-Iterative-Pruning is budget feasible and OPT ≤ 64·v(S) for submodular v
-- statement:
--   Let $N = \{0, \dots, n-1\}$ be a set of bidders with costs $c_i \ge 0$, let $B > 0$ be the budget, and let $v : 2^N \to \mathbb{R}_{\ge 0}$ be a non-negative **submodular** valuation, i.e. $v(S) + v(T) \ge v(S \cap T) + v(S \cup T)$ for all $S, T \subseteq N$. The valuation need not be monotone. Let $\mathrm{USM}$ be any map sending each $X \subseteq N$ to a subset $\mathrm{USM}(X) \subseteq X$ with $2\,v(\mathrm{USM}(X)) \ge v(Y)$ for all $Y \subseteq X$. Let $S$ and $p$ be the winning set and the prices returned by Simultaneous-Iterative-Pruning (Mechanism 3) with subroutine $\mathrm{USM}$. Then
--
--   $$\sum_{i \in S} p_i \le B \qquad\text{and}\qquad v(O) \le 64\, v(S) \ \text{ for every } O \subseteq N \text{ with } \sum_{i \in O} c_i \le B.$$
--
--   So the mechanism is budget feasible and achieves a 64-approximation of $OPT$, the largest value of a set of bidders whose total cost fits in the budget. It is the first deterministic budget-feasible mechanism with a constant approximation ratio for general (non-monotone) submodular valuations.
--
--   **Formalization Note**
--   1. The approximation is stated as $v(O) \le 64 v(S)$ for every budget-feasible $O$. This avoids dividing by $v(S)$ and avoids defining $OPT$ as a supremum.
--   2. $B > 0$ is added (§2 says only "a budget $B$"): every price offered is a multiple of $B/\widetilde{OPT}$, and with $B = 0$ every mechanism pays nothing.
--   3. No normalization $v(\emptyset) = 0$ is assumed.
--   4. The subroutine is universally quantified, because the proof uses only its 2-approximation guarantee. The paper's example, the algorithm of Buchbinder et al. [9], is randomized; a deterministic mechanism needs a deterministic 2-approximation, such as the one of Buchbinder and Feldman (2018).
--   5. "Deterministic", "polynomial-time" and "clock auction" are not separate statements. A Lean function is deterministic, running time is not formalized, and the clock-auction property (prices never increase, a rejecting bidder never returns) is built into the definition of the mechanism.
--   6. The phases are run with fuel; the definition of the mechanism explains why the fuel is never exhausted unless $v \equiv 0$.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 12, Theorem 5 (proof on pp. 12–14)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_NonMonotone_Mechanism

namespace BudgetClock.NonMonotone

/-- Theorem 5, p. 12: for every non-negative submodular valuation `v` and every subroutine `usm`
returning a subset of its input of value at least half the best subset, Simultaneous-Iterative-
Pruning returns a set `S` that is budget feasible at its prices and satisfies `OPT ≤ 64 v(S)`
(stated as `v(O) ≤ 64 v(S)` for every budget-feasible `O`). -/
theorem theorem_5 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S)
    (hsub : NonmonotoneSubmod.Shared.Submodular v)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (B : ℝ) (hB : 0 < B)
    (usm : Finset (Fin n) → Finset (Fin n))
    (husm : ∀ X, usm X ⊆ X ∧ ∀ Y ⊆ X, v Y ≤ 2 * v (usm X)) :
    (∑ i ∈ (simultaneousIterativePruning v c B usm).1,
        (simultaneousIterativePruning v c B usm).2 i ≤ B) ∧
      ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
        v O ≤ 64 * v (simultaneousIterativePruning v c B usm).1 := by sorry

end BudgetClock.NonMonotone
