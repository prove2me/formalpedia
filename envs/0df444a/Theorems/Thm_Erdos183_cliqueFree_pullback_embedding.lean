-- Prove2me | Theorems.Thm_Erdos183_cliqueFree_pullback_embedding
-- name    : Erdos183.cliqueFree_pullback_embedding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:15:22.26556+00:00
-- url     : https://prove2.me/theorems/24002fa8-5c27-486d-b575-c8a687464095
-- title:
--   Triangle-freeness is inherited by restriction along an embedding
-- statement:
--   Let $C$ be an edge-labelling of a graph on $V$ by colours in $K$ whose every colour class is triangle-free, and let $f : U \hookrightarrow V$ be an injection. Then every colour class of the pulled-back colouring $C \circ f$ is triangle-free as well.
--
--   Restricting a triangle-free colouring to a subset of the vertices therefore again gives a triangle-free colouring — the property required to feed the output of one stage of the recursive construction into the next.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L36-L46

import Definitions.Def_erdos183_core
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.cliqueFree_pullback_embedding {U V K : Type*}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (f : U ↪ V)
    (hC : ∀ colour : K, (C.labelGraph colour).CliqueFree 3) :
    ∀ colour : K, ((C.pullback f).labelGraph colour).CliqueFree 3 := by sorry
