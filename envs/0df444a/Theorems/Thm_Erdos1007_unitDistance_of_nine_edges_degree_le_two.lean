-- Prove2me | Theorems.Thm_Erdos1007_unitDistance_of_nine_edges_degree_le_two
-- name    : Erdos1007.unitDistance_of_nine_edges_degree_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:54:00.246489+00:00
-- url     : https://prove2.me/theorems/c3bdf7c8-6b49-564c-aba3-50b74d907453
-- title:
--   Erdos1007: unit Distance of nine edges degree le two
-- statement:
--   A finite graph with nine edges and a vertex of degree one or two admits an injective
--   placement in `ℝ³` in which every edge has length one (blueprint node `lem:min-degree`).
--
--   The induced subgraph on `V \ {u}` has `9 - G.degree u` edges. Degree one leaves eight. Degree
--   two leaves seven, and the edge between the two neighbours brings the count to at most eight.
--   `unitDistance_of_edgeFinset_card_le_eight` places that graph, and
--   `unitDistance_extend_degree_le_two` restores `u`. The hypothesis `0 < G.degree u` keeps the
--   degree equal to one or two: an isolated vertex leaves all nine edges on `V \ {u}`.
--
--   Chaffee–Noble, the argument of Theorem 7.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/LowDegree.lean#L55-L137
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/LowDegree.lean#L55-L137

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Erdos1007_Geometry_EightEdges
public import Definitions.Def_Erdos1007_Geometry_Reattach
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_Erdos1007_Geometry_LowDegree
set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph Metric
public section
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

theorem Erdos1007.unitDistance_of_nine_edges_degree_le_two
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) {u : V} (hdeg : G.degree u ≤ 2)
    (hpos : 0 < G.degree u) :
    ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ a b, G.Adj a b → dist (f a) (f b) = 1 := by sorry
