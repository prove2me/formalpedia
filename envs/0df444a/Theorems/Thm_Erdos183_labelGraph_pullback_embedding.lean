-- Prove2me | Theorems.Thm_Erdos183_labelGraph_pullback_embedding
-- name    : Erdos183.labelGraph_pullback_embedding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T00:15:10.652749+00:00
-- url     : https://prove2.me/theorems/7947187e-0178-4517-b9f9-32f20c2698eb
-- title:
--   Pullback of an edge-labelling commutes with taking colour classes
-- statement:
--   Let $C$ be an edge-labelling of a graph on vertex set $V$ by colours in $K$, and let $f : U \hookrightarrow V$ be an injection. Pulling $C$ back along $f$ and then extracting the colour class of a given colour yields the same graph as extracting the colour class first and then taking the preimage under $f$:
--
--   $$(C \circ f)^{-1}(\text{colour}) \;=\; f^{*}\big(C^{-1}(\text{colour})\big).$$
--
--   This is the compatibility lemma that lets the construction restrict a colouring to a subset of vertices without disturbing its colour classes.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L12-L34

import Definitions.Def_erdos183_core
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

open Filter Finset SimpleGraph
open scoped Topology
open Erdos183

theorem Erdos183.labelGraph_pullback_embedding {U V K : Type*}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (f : U ↪ V) (colour : K) :
    (C.pullback f).labelGraph colour = (C.labelGraph colour).comap f := by sorry
