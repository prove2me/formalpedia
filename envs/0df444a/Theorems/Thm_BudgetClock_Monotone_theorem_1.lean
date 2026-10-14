-- Prove2me | Theorems.Thm_BudgetClock_Monotone_theorem_1
-- name    : BudgetClock.Monotone.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:27.842961+00:00
-- url     : https://prove2.me/theorems/0f6e1b76-97ea-440a-88e7-2285b8545796
-- title:
--   Theorem 1, p. 7 — Iterative-Pruning is budget feasible and OPT ≤ 4.75 · v(W) for monotone submodular v
-- statement:
--   Let $N$ be a finite set of $n$ bidders, $v : 2^N \to \mathbb R_{\ge 0}$ a monotone submodular valuation, $c_i \ge 0$ the private cost of bidder $i$, and $B > 0$ the budget. Run the clock auction Iterative-Pruning (Mechanism 1 followed by Maximize-Value), which outputs a winning set $W$ and final prices $(p_i)_{i\in N}$. Then
--
--   1. the mechanism is **budget feasible**: $\sum_{i \in W} p_i \le B$;
--   2. it achieves a **4.75-approximation**: every set $O \subseteq N$ with $\sum_{i \in O} c_i \le B$ satisfies
--   $$v(O) \le 4.75\; v(W),$$
--   i.e. $\mathrm{OPT} \le 4.75\, v(W)$.
--
--   This is the first deterministic budget-feasible mechanism with a constant approximation factor for monotone submodular valuations, and it is a clock auction, so it is obviously strategyproof for the bidders.
--
--   **Formalization Note** The approximation is stated as $v(O) \le 4.75\,v(W)$ for every budget-feasible $O$, which avoids both a supremum and a division by $v(W)$. $B > 0$ is added (§2 only says "a budget $B$"); every price the mechanism offers is proportional to $B$. The theorem's "polynomial-time", "deterministic" and "clock auction" clauses have no separate Lean content: the mechanism is a Lean function, and every price update is a minimum with the previous price. Ties in every argmax are broken by the least bidder index. The output's prices are the final clock prices; the theorem does not claim $c_i \le p_i$ for every winner (the bidder of $S_1$ is never asked to accept a price).
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 7, Theorem 1 (proof: pp. 9–10 and Appendix A.1, pp. 19–21)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_BudgetClock_Monotone_Mechanism

namespace BudgetClock.Monotone

/-- Theorem 1, p. 7: for monotone submodular `v`, Iterative-Pruning is budget feasible at its final
prices and achieves a 4.75-approximation: `OPT ≤ 4.75 · v(W)`. -/
theorem theorem_1 {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : ∀ S, 0 ≤ v S) (hmono : IsMonotone v)
    (hsub : NonmonotoneSubmod.Shared.Submodular v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (B : ℝ) (hB : 0 < B) :
    (∑ i ∈ (iterativePruning v c B).1, (iterativePruning v c B).2 i ≤ B) ∧
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
      v O ≤ (19 / 4 : ℝ) * v (iterativePruning v c B).1 := by sorry

end BudgetClock.Monotone
