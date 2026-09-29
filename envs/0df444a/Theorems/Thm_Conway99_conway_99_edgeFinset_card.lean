-- Prove2me | Theorems.Thm_Conway99_conway_99_edgeFinset_card
-- name    : Conway99.conway_99_edgeFinset_card
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T16:14:42.526733+00:00
-- url     : https://prove2.me/theorems/4ad3a2c3-30ab-4dcb-8162-c5a499352aec
-- title:
--   A $99$-graph has exactly $693$ edges
-- statement:
--   Any strongly regular graph with parameters $(99,14,1,2)$ has exactly $693$ edges.
--
--   This is the handshake identity: the graph is $14$-regular on $99$ vertices, so the number of edges is $99 \cdot 14 / 2 = 693$. The statement is conditional on the existence of such a graph, which is Conway's open problem; it fixes one of the basic invariants any hypothetical $99$-graph must have.
-- source:
--   Handshake identity for the parameters of Conway's 99-graph problem; https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Conway99

theorem conway_99_edgeFinset_card {V : Type*} [Fintype V] [DecidableEq V]
    {g : SimpleGraph V} [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) :
    g.edgeFinset.card = 693 := by sorry

end Conway99
