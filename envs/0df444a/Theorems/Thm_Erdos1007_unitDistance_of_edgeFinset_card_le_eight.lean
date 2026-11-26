-- Prove2me | Theorems.Thm_Erdos1007_unitDistance_of_edgeFinset_card_le_eight
-- name    : Erdos1007.unitDistance_of_edgeFinset_card_le_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:54:01.298018+00:00
-- url     : https://prove2.me/theorems/f4799cd0-8d58-4307-a22a-690782897b0b
-- title:
--   Erdos1007: unit Distance of edge Finset card le eight
-- statement:
--   Every finite graph with at most eight edges admits an injective placement in `ℝ³` in which
--   every edge has length one (blueprint node `lem:eight-edges`).
--
--   The proof is by induction on `|V| + |E|`. The empty vertex set is placed by the empty function.
--   If `u` has degree at most two, the induced subgraph on `V \ {u}`, with an edge between the two
--   neighbours when the degree is two, has fewer vertices and no more edges, so the inductive
--   hypothesis places it and `unitDistance_extend_degree_le_two` restores `u`. Otherwise every degree
--   is at least three, hence `3 |V| ≤ 2 |E| ≤ 16`. Thus `|V| ≤ 5`, and `|V| ≥ 4` because some vertex
--   has three neighbours. Four vertices forces `K₄`. Five vertices forces degree sum sixteen and the
--   degree sequence `(4, 3, 3, 3, 3)`, so the complement is a matching of two edges. Either graph
--   embeds in `K₅` minus the edge `s(3, 4)`, which is representable in `ℝ³`.
--
--   Chaffee–Noble, Theorem 6.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/EightEdges.lean#L467-L474
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/EightEdges.lean#L467-L474

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Erdos1007_Geometry_CompleteMinusEdge
public import Definitions.Def_Erdos1007_Geometry_Reattach
public import Definitions.Def_Erdos1007_Geometry_UnitDistanceComap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Erdos1007_Geometry_EightEdges
set_option autoImplicit false
@[expose] public section
open Erdos1007
universe u
open SimpleGraph Metric
public section

theorem Erdos1007.unitDistance_of_edgeFinset_card_le_eight
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.edgeFinset.card ≤ 8) :
    ∃ f : V → EuclideanSpace ℝ (Fin 3), Function.Injective f ∧
      ∀ u v, G.Adj u v → dist (f u) (f v) = 1 := by sorry
