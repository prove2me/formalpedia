-- Prove2me | Theorems.Thm_ComplementFreeCA_CFRounding_layers_partition
-- name    : ComplementFreeCA.CFRounding.layers_partition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:14:49.478984+00:00
-- url     : https://prove2.me/theorems/ade68374-2d4a-4c6a-8548-a462304142b1
-- title:
--   Step (ii): the layers form k allocations and partition each bundle
-- statement:
--   Let $\sigma=(S_1,\dots,S_n)$ be a preallocation in which every item appears in at most $k$ of the bundles, and let $S_i^r$ be the layers ($S_i^r$ consists of the items of $S_i$ that appear in exactly $r-1$ of $S_1,\dots,S_{i-1}$). Then:
--
--   1. for every $1\le r\le k$ the bundles $S_1^r,\dots,S_n^r$ are pairwise disjoint, so they form a valid allocation;
--   2. for every bidder $i$,
--   $$S_i=\bigcup_{r=1}^{k} S_i^r;$$
--   3. for every bidder $i$ and indices $r\ne r'$ with $r,r'\ge1$, the layers $S_i^r$ and $S_i^{r'}$ are disjoint.
--
--   Thus each $S_i$ is the disjoint union of its $k$ layers, and each layer index yields a feasible allocation. This is step (ii) of the proof of Theorem 3.1.
--
--   **Formalization Note** Parts 1 and 3 hold for any preallocation; the count bound is what makes $k$ layers enough to cover $S_i$ in part 2.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 6, §3.1, proof of Theorem 3.1, step (ii); construction of p. 5, algorithm step (ii)

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction
import Definitions.Def_ComplementFreeCA_CFRounding_Algorithm

namespace ComplementFreeCA.CFRounding

theorem layers_partition {n m : ℕ} (σ : Fin n → Finset (Fin m)) (k : ℕ)
    (hcount : ∀ j, count σ j ≤ k) :
    (∀ r : ℕ, 1 ≤ r → r ≤ k → IsAllocation (fun i => layer σ i r)) ∧
    (∀ i : Fin n, σ i = (Finset.Icc 1 k).biUnion (fun r => layer σ i r)) ∧
    (∀ (i : Fin n) (r r' : ℕ), 1 ≤ r → 1 ≤ r' → r ≠ r' →
      Disjoint (layer σ i r) (layer σ i r')) := by sorry

end ComplementFreeCA.CFRounding
