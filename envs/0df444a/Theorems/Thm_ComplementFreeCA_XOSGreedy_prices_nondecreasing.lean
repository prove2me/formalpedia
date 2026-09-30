-- Prove2me | Theorems.Thm_ComplementFreeCA_XOSGreedy_prices_nondecreasing
-- name    : ComplementFreeCA.XOSGreedy.prices_nondecreasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:51:06.700477+00:00
-- url     : https://prove2.me/theorems/cc8de41e-056a-4ffa-903f-128da11d66fc
-- title:
--   Lemma 3.5 — prices are nondecreasing during the greedy algorithm
-- statement:
--   Let $v_1,\dots,v_n$ be XOS valuations on the items $M=\{1,\dots,m\}$ given by XOS expressions, and let the greedy price-update algorithm of §3.3 run with any demand oracle and any XOS oracle for this profile. Write $p^k_j$ for the price of item $j$ after stage $k$ ($p^0=0$). Then for every item $j$ and all stages $k\le k'$,
--   $$
--   p^k_j\le p^{k'}_j .
--   $$
--
--   The paper states: the prices assigned to the items throughout the execution of the algorithm are nondecreasing. In the proof of Lemma 3.6 this is what allows replacing $p^{i-1}$ by the final prices $p^n$.
--
--   **Formalization Note** Stages are indexed by natural numbers; after stage $n$ the state is constant, so the statement for all $k\le k'$ contains the paper's range $0\le k\le k'\le n$.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 8, Lemma 3.5

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model
import Definitions.Def_ComplementFreeCA_XOSGreedy_GreedyRun

namespace ComplementFreeCA.XOSGreedy

theorem prices_nondecreasing {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hdem : IsDemandOracle E dem) (hcl : IsXOSOracle E cl)
    (k k' : ℕ) (hkk : k ≤ k') (j : Fin m) :
    greedyPrices dem cl k j ≤ greedyPrices dem cl k' j := by sorry

end ComplementFreeCA.XOSGreedy
