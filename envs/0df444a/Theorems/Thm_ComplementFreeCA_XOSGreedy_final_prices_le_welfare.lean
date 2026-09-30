-- Prove2me | Theorems.Thm_ComplementFreeCA_XOSGreedy_final_prices_le_welfare
-- name    : ComplementFreeCA.XOSGreedy.final_prices_le_welfare
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:48:48.74287+00:00
-- url     : https://prove2.me/theorems/2853a73d-a0cb-47fb-96f6-a1856144c468
-- title:
--   Lemma 3.4 — the final prices are at most the welfare of the greedy allocation
-- statement:
--   Let $v_1,\dots,v_n$ be XOS valuations on the items $M=\{1,\dots,m\}$ given by XOS expressions, and let the greedy price-update algorithm of §3.3 run with any demand oracle and any XOS oracle for this profile. Write $p^n$ for the item prices after the last stage and $A_1,\dots,A_n$ for the allocation the algorithm generates, and $p^n(M)=\sum_{j\in M}p^n_j$. Then
--   $$
--   p^n(M)\le \sum_{i=1}^n v_i(A_i).
--   $$
--
--   Together with Lemma 3.6 this gives the approximation guarantee of Theorem 3.3: the final prices are a lower bound on the algorithm's welfare.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 8, Lemma 3.4

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model
import Definitions.Def_ComplementFreeCA_XOSGreedy_GreedyRun

namespace ComplementFreeCA.XOSGreedy

theorem final_prices_le_welfare {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hdem : IsDemandOracle E dem) (hcl : IsXOSOracle E cl) :
    ∑ j, greedyPrices dem cl n j ≤ welfare E (greedyAlloc dem cl) := by sorry

end ComplementFreeCA.XOSGreedy
