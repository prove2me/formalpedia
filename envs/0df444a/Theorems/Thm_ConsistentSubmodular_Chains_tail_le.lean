-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_tail_le
-- name    : ConsistentSubmodular.Chains.tail_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:03.675185+00:00
-- url     : https://prove2.me/theorems/b36d86f6-c6b5-427c-a66b-3e42ccf3dfd6
-- title:
--   Tail after a vertex $z\le L$ collapses to the edge $z\to1$
-- statement:
--   Let $q=q^\star$, $L=\frac{1}{1-q}$, and $\varphi(x,y)=1-\frac yx-q(x-1)$. For a list $(d_0,\dots,d_N)$ let the chain value be $\sum_{j<N}\varphi(d_j,d_{j+1})$ (the value of a list with fewer than two entries is $0$). Let $(z,\text{rest})$ be a descending chain (weakly decreasing, all entries at least $1$, last entry $1$) with $z\le L$. Then
--   $$\operatorname{val}(z,\text{rest})\;\le\;\varphi(z,1).$$
--
--   The proof collapses the tail edge by edge by inequality (16). The statement is used to reduce a long chain to a three-edge chain once the third vertex is below $L$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveChains.lean#L530-L543 (`ConsistentSubmodular.Chains.tail_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem ConsistentSubmodular.Chains.tail_le (z : ℝ) (rest : List ℝ) (h : IsDescendingChain (z :: rest))
    (hzL : z ≤ collapseBound) : chainValue (z :: rest) ≤ edgeValue z 1 := by sorry
