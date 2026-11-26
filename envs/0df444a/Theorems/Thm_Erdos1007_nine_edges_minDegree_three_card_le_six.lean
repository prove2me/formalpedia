-- Prove2me | Theorems.Thm_Erdos1007_nine_edges_minDegree_three_card_le_six
-- name    : Erdos1007.nine_edges_minDegree_three_card_le_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:35.163586+00:00
-- url     : https://prove2.me/theorems/4362e40a-1c6f-4f98-bb25-03701a3e1072
-- title:
--   Erdos1007: nine edges min Degree three card le six
-- statement:
--   **At most six vertices.** A simple graph with nine edges and minimum degree at least three
--   has at most six vertices.
--
--   The handshaking lemma gives `∑ v, G.degree v = 2 * 9 = 18`, and the degree hypothesis gives
--   `3 * Fintype.card V ≤ ∑ v, G.degree v`. Blueprint node `lem:at-most-six`. Chaffee and Noble
--   pass to the five-vertex and six-vertex cases without recording this comparison.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/NineEdges.lean#L82-L89
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Combinatorics/SimpleGraph/NineEdges.lean#L82-L89

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

theorem Erdos1007.nine_edges_minDegree_three_card_le_six
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) (hdeg : ∀ v, 3 ≤ G.degree v) :
    Fintype.card V ≤ 6 := by sorry
