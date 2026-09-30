-- Prove2me | Theorems.Thm_ComplementFreeCA_XOSGreedy_optimal_welfare_le_two_final_prices
-- name    : ComplementFreeCA.XOSGreedy.optimal_welfare_le_two_final_prices
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:53:08.250965+00:00
-- url     : https://prove2.me/theorems/7e9a9f71-c059-4374-8d79-569e9aba0547
-- title:
--   Lemma 3.6 — every allocation's welfare is at most twice the final prices
-- statement:
--   Let $v_1,\dots,v_n$ be XOS valuations on the items $M=\{1,\dots,m\}$ given by XOS expressions, and let the greedy price-update algorithm of §3.3 run with any demand oracle and any XOS oracle for this profile, with final prices $p^n$. Then for every allocation $O_1,\dots,O_n$ (pairwise disjoint bundles),
--   $$
--   \sum_{i=1}^n v_i(O_i)\le 2\,p^n(M),\qquad p^n(M)=\sum_{j\in M}p^n_j .
--   $$
--
--   The paper states it for the optimal allocation; holding for every allocation is equivalent and needs no optimal allocation to be named. Combined with Lemma 3.4 it yields Theorem 3.3.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 8, Lemma 3.6 (proof on pp. 8–9)

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model
import Definitions.Def_ComplementFreeCA_XOSGreedy_GreedyRun

namespace ComplementFreeCA.XOSGreedy

theorem optimal_welfare_le_two_final_prices {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hdem : IsDemandOracle E dem) (hcl : IsXOSOracle E cl)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    welfare E O ≤ 2 * ∑ j, greedyPrices dem cl n j := by sorry

end ComplementFreeCA.XOSGreedy
