-- Prove2me | Theorems.Thm_Erdos1007_nine_edges_six_minDegree_three
-- name    : Erdos1007.nine_edges_six_minDegree_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:42.815686+00:00
-- url     : https://prove2.me/theorems/c173103e-406a-55df-88a3-e8d5c265a80b
-- title:
--   Erdos1007: nine edges six min Degree three
-- statement:
--   A simple graph on six vertices with nine edges and minimum degree three is isomorphic
--   to `K₃,₃`, or its complement is the hexagon `C₆`.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/SixVertices.lean#L81-L96
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/SixVertices.lean#L81-L96

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_TwoRegularSix
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.BooleanAlgebra.Basic
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_SixVertices
set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph
public section

theorem Erdos1007.nine_edges_six_minDegree_three
    {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) (hdeg : ∀ v, 3 ≤ G.degree v) :
    Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∨
      Nonempty (Gᶜ ≃g cycleGraph 6) := by sorry
