-- Prove2me | Theorems.Thm_Erdos1007_unitDistance_extend_degree_le_two
-- name    : Erdos1007.unitDistance_extend_degree_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:20.036162+00:00
-- url     : https://prove2.me/theorems/03ba388c-e439-5b56-a6eb-bfa9b93b926f
-- title:
--   Erdos1007: unit Distance extend degree le two
-- statement:
--   Re-attach a vertex `u` of degree at most two to a unit-distance placement of the induced
--   subgraph on `V \ {u}` (blueprint node `lem:reattach`).
--
--   The two neighbours of `u` are at distance one whenever the degree is exactly two. The point
--   chosen for `u` lies outside the finite image of the given placement: anywhere, if `u` is
--   isolated; on the unit sphere about its neighbour, if the degree is one; and on the circle in
--   which the two unit spheres meet, if the degree is two. Edges not incident to `u` are edges of
--   the induced subgraph, and each edge incident to `u` meets that new point at distance one.
--
--   Chaffee–Noble give the degree-two case in the argument of Theorem 6 and call the degree-one
--   case obvious.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/Reattach.lean#L233-L283
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/Reattach.lean#L233-L283

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Erdos1007_Geometry_Reattach
set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph Metric
open scoped RealInnerProductSpace
public section

theorem Erdos1007.unitDistance_extend_degree_le_two
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u : V} (hdeg : G.degree u ≤ 2) :
    (∃ f : {v : V // v ≠ u} → EuclideanSpace ℝ (Fin 3),
        Function.Injective f ∧
        ∀ a b : {v : V // v ≠ u},
          ((G.induce {v | v ≠ u}).Adj a b ∨
            (G.degree u = 2 ∧ a.1 ∈ G.neighborSet u ∧ b.1 ∈ G.neighborSet u ∧ a ≠ b)) →
          dist (f a) (f b) = 1) →
      ∃ g : V → EuclideanSpace ℝ (Fin 3), Function.Injective g ∧
        ∀ a b, G.Adj a b → dist (g a) (g b) = 1 := by sorry
