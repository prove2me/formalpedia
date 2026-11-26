-- Prove2me | Theorems.Thm_Erdos1007_nine_edges_card_ge_five
-- name    : Erdos1007.nine_edges_card_ge_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:32.837079+00:00
-- url     : https://prove2.me/theorems/a130658a-75db-4153-8b64-255e589b4578
-- title:
--   Erdos1007: nine edges card ge five
-- statement:
--   **At least five vertices.** A simple graph with nine edges has at least five vertices.
--
--   `K₄` has six edges, and `Nat.choose 4 2 = 6`, so a simple graph on at most four vertices has at
--   most six edges. Blueprint node `lem:at-least-five`.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/NineEdges.lean#L67-L74
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/NineEdges.lean#L67-L74

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Nat.Choose.Basic
public import Definitions.Def_Erdos1007_Combinatorics_SimpleGraph_NineEdges
set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph
public section

theorem Erdos1007.nine_edges_card_ge_five
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.edgeFinset.card = 9) : 5 ≤ Fintype.card V := by sorry
