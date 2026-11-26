-- Prove2me | Theorems.Thm_Erdos1007_nine_edges_iso_deleteEdge
-- name    : Erdos1007.nine_edges_iso_deleteEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:35.416658+00:00
-- url     : https://prove2.me/theorems/76770a4d-3256-4fbf-a87a-852de310d270
-- title:
--   Erdos1007: nine edges iso delete Edge
-- statement:
--   A simple graph on five vertices with nine edges is the complete graph with one edge deleted.
--
--   Nine edges force every degree to be at least three. The degree sum is then eighteen, so the
--   degrees are three `4`s and two `3`s; each degree-`4` vertex is adjacent to every other vertex,
--   and the complement is the edge joining the two degree-`3` vertices.
--
--   Chaffee and Noble assert that the degree sequence `(4, 4, 4, 3, 3)` corresponds solely to this
--   graph, in the proof of their Theorem 7.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/FiveVertices.lean#L191-L201
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/FiveVertices.lean#L191-L201

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_FiveVertices
set_option autoImplicit false
@[expose] public section
open Erdos1007
open Finset SimpleGraph
public section

theorem Erdos1007.nine_edges_iso_deleteEdge
    {G : SimpleGraph (Fin 5)} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) :
    ∃ a b : Fin 5, a ≠ b ∧
      Nonempty (G ≃g (⊤ : SimpleGraph (Fin 5)).deleteEdges {s(a, b)}) := by sorry
