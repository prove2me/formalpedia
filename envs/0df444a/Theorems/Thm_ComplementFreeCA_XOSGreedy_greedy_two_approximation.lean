-- Prove2me | Theorems.Thm_ComplementFreeCA_XOSGreedy_greedy_two_approximation
-- name    : ComplementFreeCA.XOSGreedy.greedy_two_approximation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:53:38.4452+00:00
-- url     : https://prove2.me/theorems/4bdddb3d-8679-4cb0-be5d-a259bd04042d
-- title:
--   Theorem 3.3 — the greedy price-update algorithm is a 2-approximation for XOS bidders
-- statement:
--   Let $v_1,\dots,v_n$ be XOS valuations on the items $M=\{1,\dots,m\}$, each given by an XOS expression (a nonempty set of additive clauses with nonnegative item values, $v_i(S)=\max_k w^i_k(S)$). Run the greedy price-update algorithm of §3.3: bidders are processed in order $1,\dots,n$; bidder $i$ takes its demand $S_i$ at the current item prices (removing those items from earlier bidders), and the prices of the items of $S_i$ are set to their values in a maximizing clause for $S_i$ in $v_i$. Let $A_1,\dots,A_n$ be the resulting allocation. Then, for **every** demand oracle and **every** XOS oracle used by the algorithm, and for every allocation $O_1,\dots,O_n$,
--   $$
--   \sum_{i=1}^n v_i(O_i)\le 2\sum_{i=1}^n v_i(A_i).
--   $$
--
--   In the paper's words, the algorithm provides a 2-approximation to the optimal allocation. It uses only demand queries and XOS queries and, unlike the LP-based algorithms of §3.1–3.2, is combinatorial.
--
--   **Formalization Note** The paper compares with the optimal allocation; the statement quantifies over every allocation, which is equivalent. The oracles are arbitrary functions meeting their specifications, so the guarantee holds for every tie-breaking in the demand and in the choice of maximizing clause. Running time is not modelled.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 8, Theorem 3.3 (proof pp. 8–9)

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model
import Definitions.Def_ComplementFreeCA_XOSGreedy_GreedyRun

namespace ComplementFreeCA.XOSGreedy

theorem greedy_two_approximation {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hdem : IsDemandOracle E dem) (hcl : IsXOSOracle E cl)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    welfare E O ≤ 2 * welfare E (greedyAlloc dem cl) := by sorry

end ComplementFreeCA.XOSGreedy
