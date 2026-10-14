-- Prove2me | Theorems.Thm_BudgetClock_PostedSym_case_2
-- name    : BudgetClock.PostedSym.case_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:24.601412+00:00
-- url     : https://prove2.me/theorems/b1ed1731-575a-4d1e-9193-c4f3af39f1dd
-- title:
--   Theorem 15 proof, Case 2, p. 28 (corrected) — if k ≥ 1 bidders accept, OPT ≤ (2 ln n + 2)·v(W)
-- statement:
--   Let $n \ge 2$, let $v$ be a symmetric submodular valuation on $n$ bidders, let $B > 0$ be the budget and $0 \le c_i \le B$ the costs, and let $j$ be any bidder. Suppose that during the scan of Mechanism 5 at least one bidder of $[n]\setminus\{j\}$ accepts its offer, and let $W$ be the returned winning set. Then every set $O$ of bidders with $\sum_{i\in O} c_i \le B$ satisfies
--   $$v(O) \le (2\ln n + 2)\, v(W).$$
--
--   This is the second case of the proof of Theorem 15. If $k$ bidders accept, every rejected bidder was offered at least $\tfrac{B}{k\cdot 2\ln n}$, so a budget-feasible set contains fewer than $k\cdot 2\ln n$ rejected bidders, besides the $k$ winners and possibly the set-aside bidder $j$.
--
--   **Formalization Note.** The page concludes $\mathrm{OPT}/v(\mathcal M) < 2\ln n + 1$, which is false: it does not count the set-aside bidder $j$, who is not offered anything once some bidder accepted but may belong to the optimal set. Counterexample: $n = 10$, $r_i = 1$ for all $i$, the first scanned bidder and $j$ cost $0$, every other bidder costs $\tfrac{B}{2\ln 10} + \delta$ for small $\delta > 0$. Then $k = 1$, $v(W) = 1$, and the budget-feasible set made of $j$, the winner and $\lfloor 2\ln 10\rfloor = 4$ other bidders has value $6 > 2\ln 10 + 1 \approx 5.61$. Counting $j$ gives the constant $2\ln n + 2$ stated here.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 28, proof of Theorem 15, Case 2 (constant corrected from 2 ln n + 1 to 2 ln n + 2)

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting

namespace BudgetClock.PostedSym

theorem case_2 (n : ℕ) (hn : 2 ≤ n) (v : Finset (Fin n) → ℝ) (hv : IsSymmetricSubmodular n v)
    (B : ℝ) (hB : 0 < B) (c : Fin n → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B)
    (j : Fin n) (hsome : 1 ≤ (scan n B c j).count) :
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
      v O ≤ (2 * Real.log n + 2) * v (mech5 n B c j).1 := by sorry

end BudgetClock.PostedSym
