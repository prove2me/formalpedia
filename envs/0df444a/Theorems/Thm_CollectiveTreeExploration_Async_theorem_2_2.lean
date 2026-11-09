-- Prove2me | Theorems.Thm_CollectiveTreeExploration_Async_theorem_2_2
-- name    : CollectiveTreeExploration.Async.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:13:09.828399+00:00
-- url     : https://prove2.me/theorems/38af49fe-c4d4-46d3-8479-33303ed5069e
-- title:
--   Theorem 2.2 — continuous tree-mining bound
-- statement:
--   Let $k\ge2$. There exists a strategy for the continuous tree-mining game with $k$ miners whose cumulative cost, in every play in which the tree has depth at most $D$, is bounded by
--   $$f(k,D)\le\frac{8192}{\log(4/3)}\,k\log^2(2k)\,D=O(k\log^2(k)D).$$
--
--   This is the new tree-mining bound of the paper; through the reduction of Theorem 2.1 it gives the exploration guarantee of Theorem 1.1. The strategy of §3.1 is a witness (Propositions 3.2 and 3.3).
--
--   Differences from the source:
--   - encoding: finite rooted weighted trees and leaf configurations of total mass k → finite sets of natural-number labels, a parent map, positive non-root lengths and zero-extended leaf masses, with descendant paths including the lower endpoint only; reason: every source tree admits these labels, with no size, length or mass restriction; tree validity uses the published general tree type without its separate HST restrictions
--   - encoding: the explicit bound followed by O(k log²(k) D) → the exact uniform coefficient 8192/log(4/3) multiplying k log²(2k) D; reason: for k ≥ 2, log(2k) ≤ 2 log k, so the explicit inequality includes the stated asymptotic order
-- source:
--   Romain Cosson, Laurent Massoulié, Polylogarithmic Collective Tree Exploration, STOC 2027 submission #263 (October 2026), source.pdf sha256 54f5e43ddf9269e11a2fff4aa4b0ea62348afe16a38aba551313f43cbf3e00e0; Theorem 2.2, p.6; k ≥ 2 fixed in §3.1, p.7

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_TreeMining

namespace CollectiveTreeExploration.Async

open scoped BigOperators ENNReal

/-- **Theorem 2.2** (continuous tree-mining bound, p.6). For every `k ≥ 2` there is a tree-mining
strategy whose cumulative cost, whenever the tree has depth at most `D`, is at most
`8192 / log(4/3) · k · log²(2k) · D`. -/
theorem theorem_2_2 (k : ℕ) (hk : 2 ≤ k) :
    ∃ S : CTMStrategy k, MaintainsCost S
      (fun D => 8192 / Real.log (4 / 3) * (k : ℝ) * Real.log (2 * (k : ℝ)) ^ 2 * D) := by sorry

end CollectiveTreeExploration.Async
