-- Prove2me | Theorems.Thm_BudgetClock_PostedSym_payment_bound
-- name    : BudgetClock.PostedSym.payment_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:30.48776+00:00
-- url     : https://prove2.me/theorems/e0247416-24eb-4b20-af72-fd4caefc4aa7
-- title:
--   Theorem 15 proof, p. 27 — Mechanism 5 never exhausts the budget
-- statement:
--   Let $n \ge 2$ bidders have costs $0 \le c_i \le B$, where $B > 0$ is the budget, and let $j$ be any bidder. Run Mechanism 5 with set-aside bidder $j$. Write $W'$ for the set of bidders that accept during the scan of $[n]\setminus\{j\}$ and $p_i$ for the price offered to bidder $i$; write $W$ for the final winning set. Then
--   $$\sum_{i \in W'} p_i < B \qquad\text{and}\qquad \sum_{i \in W} p_i \le B .$$
--
--   The first inequality is the paper's statement that "at any time of the execution of the mechanism, we would not exhaust the budget"; the second is budget feasibility of the mechanism's output, which includes the payment $B$ to $j$ when nobody else accepted.
--
--   **Formalization Note.** The proof on p. 27 bounds the payment by $(1 + 1 + \tfrac12 + \cdots + \tfrac1{n-1})\tfrac{B}{2\ln n} \le \tfrac{\ln(n-1)+2}{2\ln n}B < B$; the last inequality fails for $2 \le n \le 6$ (at $n=2$ the middle term is $\approx 1.44\,B$). Only $n-1$ bidders are scanned, so at most $n-1$ prices are paid and the total is at most $(1 + H_{n-2})\tfrac{B}{2\ln n}$, which is below $B$ for every $n \ge 2$. The theorem states the claim, not the printed chain. The hypothesis $n \ge 2$ makes $\ln n > 0$; $c_i \le B$ is the paper's standing assumption for Mechanism 5 (p. 27).
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 27, proof of Theorem 15, first paragraph

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting

namespace BudgetClock.PostedSym

theorem payment_bound (n : ℕ) (hn : 2 ≤ n) (B : ℝ) (hB : 0 < B)
    (c : Fin n → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B) (j : Fin n) :
    (∑ i ∈ (scan n B c j).winners, (scan n B c j).price i < B) ∧
    (∑ i ∈ (mech5 n B c j).1, (mech5 n B c j).2 i ≤ B) := by sorry

end BudgetClock.PostedSym
