-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_fact_13
-- name    : BuchiRabinIndex.LowerBound.fact_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:52.777324+00:00
-- url     : https://prove2.me/theorems/e44d50fc-6e84-4cb1-8201-63e44ba30834
-- title:
--   Fact 13 — node counts by weight
-- statement:
--   Let $n\ge1$ and let $T^{(n)}$ be the unique $n$-full ordered tree. Then
--   $$|T^{(n)}|=2^{n-1},\qquad \{x\in T^{(n)}:\operatorname{weight}(x)=0\}=\{\epsilon\}.$$
--   For every integer $w$ with $0<w\le n-1$, exactly $2^{w-1}$ nodes have weight $w$.
--
--   This counts every possible implicit history-tree node name, and supplies the level counts used in the coexistence graph.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: the unique n-full ordered tree of Definition 12 → the explicitly enumerated positive words of weight at most n−1; reason: this is the same finite tree; no size is fixed
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Fact 13, p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, fact 13; statement only. -/
theorem fact_13 (n : ℕ) (hn : 1 ≤ n) :
    (fullTree n).card = 2 ^ (n - 1) ∧
    (fullTree n).filter (weight · = 0) = {[]} ∧
    ∀ w, 0 < w → w ≤ n - 1 →
      ((fullTree n).filter (weight · = w)).card = 2 ^ (w - 1) := by sorry

end BuchiRabinIndex.LowerBound
