-- Prove2me | Theorems.Thm_Erdos180_encodeFiniteGraph_isBipartite
-- name    : Erdos180.encodeFiniteGraph_isBipartite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:22:50.235414+00:00
-- url     : https://prove2.me/theorems/b4507f87-5f43-49fe-8beb-6caa1fb6a2d4
-- title:
--   Encoding preserves bipartiteness
-- statement:
--   The canonical encoding of a bipartite finite graph is bipartite. The last transport step
--   for the structural properties of the members of $\mathcal{F}$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L9170-L9176

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Erdos180
open Finset SimpleGraph

theorem Erdos180.encodeFiniteGraph_isBipartite
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hbipartite : graph.IsBipartite) :
    (encodeFiniteGraph graph).graph.IsBipartite := by sorry
