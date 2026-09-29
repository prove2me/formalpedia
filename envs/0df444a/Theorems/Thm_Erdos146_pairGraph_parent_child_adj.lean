-- Prove2me | Theorems.Thm_Erdos146_pairGraph_parent_child_adj
-- name    : Erdos146.pairGraph_parent_child_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:44:05.616281+00:00
-- url     : https://prove2.me/theorems/76ca22e8-0cd1-45d0-aa32-5f560d806807
-- title:
--   Parents are adjacent to their child
-- statement:
--   Structural fact about the layered graph $H$ of Section 6. The counterexample graph $H$ is built in layers (Section 6): starting from a layer $V_0$ of size $L_0$, each subsequent layer is $V_i = \binom{V_{i-1}}{2}$, and every vertex $\{a,b\} \in V_i$ is joined to its two parents $a, b \in V_{i-1}$. Fact 6.1 records that the result is connected, bipartite and 2-degenerate. Each vertex $\{a,b\}$ of layer $V_i$ is adjacent to both of its parents $a, b \in V_{i-1}$ — the defining adjacency of the construction.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L12121-L12148

import Definitions.Def_erdos146_core2
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairGraph_parent_child_adj
    (baseSize depth layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (child : PairLayer baseSize (layer + 1))
    (parent : PairLayer baseSize layer)
    (hparent : parent ∈ child.val) :
    (pairParentSystem baseSize depth).graph.Adj
      (pairLayerEmbedding baseSize depth (layer + 1) hlayer child)
      (pairLayerEmbedding baseSize depth layer (by omega) parent) := by sorry
