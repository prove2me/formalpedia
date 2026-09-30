-- Prove2me | Theorems.Thm_ComplementFreeCA_ValueQuery_alg_maximal_in_range
-- name    : ComplementFreeCA.ValueQuery.alg_maximal_in_range
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:55:50.046923+00:00
-- url     : https://prove2.me/theorems/8661d252-1a6b-467a-85cb-6ad10381d033
-- title:
--   Proof of Theorem 5.1 — the value-query algorithm is maximal in range
-- statement:
--   Consider the algorithm of §5.2 on report profiles $b=(b_1,\dots,b_n)$ of valuations on bundles of $M=\{1,\dots,m\}$: compute a maximum-weight matching $P$ between items and bidders with edge costs $b_i(\{j\})$, and a bidder $t$ maximizing $b_i(M)$; if $b_t(M)$ is strictly larger than the weight of $P$, give all items to $t$, otherwise give every item matched by $P$ to its matched bidder. Let $R$ be the set of allocations that give all of $M$ to a single bidder, together with the allocations (pairwise disjoint bundles) in which every bidder receives at most one item.
--
--   Then, for every choice of the maximum-weight matching and of the top bidder as functions of the reports, the algorithm is **maximal in range** with range $R$ on the normalized valuations: whenever $b_k(\emptyset)=0$ for every $k$, the output lies in $R$ and
--   $$\sum_i b_i(a_i)\;\le\;\sum_i b_i\big(\mathrm{ALG}(b)_i\big)\qquad\text{for all } a\in R.$$
--
--   Combined with the §5.1 observation on maximal-in-range rules, this is the incentive-compatibility half of Theorem 5.1.
--
--   **Formalization Note** The statement is over all normalized report profiles, a larger domain than the complement-free valuations of Theorem 5.1; normalization makes the welfare of "all items to $i$" equal to $b_i(M)$ and the welfare of a one-item-each allocation equal to the weight of the corresponding matching.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 11, proof of Theorem 5.1, second paragraph ('The algorithm is clearly a maximal-in-range algorithm …'), with §5.2 steps (i)–(iii)

import Mathlib
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic

open Finset

namespace ComplementFreeCA.ValueQuery

/-- Proof of Theorem 5.1 (p. 11): the algorithm of §5.2 is maximal in range, with range
`ValueQueryRange`, on normalized reports, for every maximum-weight matching rule and every
top-bidder rule. -/
theorem alg_maximal_in_range {n m : ℕ}
    (mat : (Fin n → Finset (Fin m) → ℝ) → Fin m → Option (Fin n))
    (top : (Fin n → Finset (Fin m) → ℝ) → Fin n)
    (hmat : IsMaxWeightMatchingRule mat) (htop : IsTopBidderRule top) :
    IsMaximalInRange IsNormalized ValueQueryRange (alg mat top) := by sorry

end ComplementFreeCA.ValueQuery
