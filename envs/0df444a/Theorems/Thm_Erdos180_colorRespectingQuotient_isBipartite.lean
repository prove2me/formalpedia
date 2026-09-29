-- Prove2me | Theorems.Thm_Erdos180_colorRespectingQuotient_isBipartite
-- name    : Erdos180.colorRespectingQuotient_isBipartite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:22:30.289894+00:00
-- url     : https://prove2.me/theorems/4a7ee5c8-c3bf-4ca2-bdfa-e69514124685
-- title:
--   Admissible quotients are bipartite
-- statement:
--   The quotient of a properly two-coloured graph by a colour-respecting identification is
--   bipartite.
--
--   This is condition (1) of Definition 2.2 doing its work: an admissible equivalence may only
--   identify vertices of the same colour, which keeps the quotient bipartite and prevents loops.
--   It is why every member of $\mathcal{F}$ is bipartite, strengthening Theorem 1.1.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L9131-L9168

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Erdos180
open Finset SimpleGraph

theorem Erdos180.colorRespectingQuotient_isBipartite
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f) :
    (quotientGraph graph f).IsBipartite := by sorry
