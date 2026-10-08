-- Prove2me | Theorems.Thm_FiniteStraightLineComplexOneEdgeComplementComponents
-- name    : FiniteStraightLineComplexOneEdgeComplementComponents
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T20:41:17.929189+00:00
-- url     : https://prove2.me/theorems/eed2daed-e030-4882-afca-e2f958c93cd1
-- title:
--   Finite Straight Line Complex One Edge Complement Components
-- statement:
--   Let $A\subseteq\mathbb R^2$ be the carrier of a finite normalized straight-line
--   complex
--   $$
--     A=V\cup\bigcup_{e\in E} e,
--   $$
--   where $V$ is a finite vertex set, $E$ is a finite set of nondegenerate
--   closed straight edges, the endpoints of every edge lie in $V$, no vertex lies
--   in the relative interior of an edge, and distinct edge relative interiors are
--   disjoint.  Let $\sigma=[a,b]$ be a nondegenerate closed straight segment with
--   $a,b\in V$, and suppose that its relative interior $\sigma^\circ$ is
--   disjoint from $A$.  If the complement of $A$ has only finitely many
--   complement components, then the complement of $A\cup\sigma$ has only
--   finitely many complement components.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FiniteStraightLineComplexOneEdgeComplementComponents`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FiniteStraightLineComplexOneEdgeComplementComponents.lean#L1-L334

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Convex.Between
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma FiniteStraightLineComplexOneEdgeComplementComponents
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2))
    (hA :
      A =
        (V : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2)
    (hEdgeSource :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ∈ V)
    (hEdgeTarget :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.2 ∈ V)
    (hEdgeNondegenerate :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ e.2)
    (hNoVertexInEdgeInterior :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E →
          ∀ v : EuclideanSpace ℝ (Fin 2),
            v ∈ V → v ∉ openSegment ℝ e.1 e.2)
    (hEdgeOpenInteriorsDisjoint :
      ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → f ∈ E → e ≠ f →
          Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2))
    (haV : a ∈ V)
    (hbV : b ∈ V)
    (hab : a ≠ b)
    (hNewInteriorDisjoint : Disjoint (openSegment ℝ a b) A)
    (hFiniteA :
      ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
        (∀ C ∈ comps, ComplementComponent A C) ∧
          ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
            ComplementComponent A C → C ∈ comps) :
    ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
      (∀ C ∈ comps, ComplementComponent (A ∪ segment ℝ a b) C) ∧
        ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent (A ∪ segment ℝ a b) C → C ∈ comps := by sorry
