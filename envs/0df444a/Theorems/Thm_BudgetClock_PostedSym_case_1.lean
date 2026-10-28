-- Prove2me | Theorems.Thm_BudgetClock_PostedSym_case_1
-- name    : BudgetClock.PostedSym.case_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:26.689928+00:00
-- url     : https://prove2.me/theorems/5378bb68-ca22-4453-a279-8d68d56fed4f
-- title:
--   Theorem 15 proof, Case 1, p. 28 — if no bidder accepts, W = {j} and OPT ≤ (2 ln n + 1)·v(W)
-- statement:
--   Let $n \ge 2$, let $v$ be a symmetric submodular valuation on $n$ bidders, let $B > 0$ be the budget and $0 \le c_i \le B$ the costs, and let $j$ be any bidder. Suppose that during the scan of Mechanism 5 no bidder of $[n]\setminus\{j\}$ accepts its offer. Then the mechanism returns $W = \{j\}$, and every set $O$ of bidders with $\sum_{i\in O} c_i \le B$ satisfies
--   $$v(O) \le (2\ln n + 1)\, v(W).$$
--
--   This is the first of the two cases in the proof of Theorem 15: every scanned bidder rejected $\tfrac{B}{2\ln n}$, so a budget-feasible set contains fewer than $2\ln n$ of them plus possibly $j$.
--
--   **Formalization Note.** "No agent accepts" is the hypothesis that the counter $a$ of Mechanism 5 is $0$ after the scan. The returned set contains $j$ because Mechanism 5 is formalized with $j$ joining $W$ when it accepts the offer $B$ (the proof's reading; see the definition file), and $j$ accepts since $c_j \le B$. The page writes the ratio as "$< 2\ln n + 1$"; the inequality is stated non-strictly, since equality $0 = 0$ occurs when $v \equiv 0$.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 28, proof of Theorem 15, Case 1

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting

namespace BudgetClock.PostedSym

theorem case_1 (n : ℕ) (hn : 2 ≤ n) (v : Finset (Fin n) → ℝ) (hv : IsSymmetricSubmodular n v)
    (B : ℝ) (hB : 0 < B) (c : Fin n → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B)
    (j : Fin n) (hnone : (scan n B c j).count = 0) :
    (mech5 n B c j).1 = {j} ∧
    ∀ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B →
      v O ≤ (2 * Real.log n + 1) * v (mech5 n B c j).1 := by sorry

end BudgetClock.PostedSym
