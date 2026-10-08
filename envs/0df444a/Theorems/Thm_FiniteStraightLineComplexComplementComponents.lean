-- Prove2me | Theorems.Thm_FiniteStraightLineComplexComplementComponents
-- name    : FiniteStraightLineComplexComplementComponents
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:26:23.408264+00:00
-- url     : https://prove2.me/theorems/6b21ece2-816c-4ea7-89d8-5c0af15c1b6b
-- title:
--   Finite Straight Line Complex Complement Components
-- statement:
--   Let $V$ be a finite set of points in the plane and let $E$ be a finite set
--   of nondegenerate closed straight edges.  Suppose that both endpoints of every
--   edge of $E$ lie in $V$, no vertex of $V$ lies in the relative interior of
--   an edge of $E$, and distinct edge relative interiors are disjoint.  Assume
--   also the following one-edge extension principle: whenever $A$ is the carrier
--   of a finite normalized straight-line complex with vertex set $V_0$ and edge
--   set $E_0$, and $[a,b]$ is a nondegenerate edge with $a,b\in V_0$ whose
--   relative interior is disjoint from $A$, finiteness of the complement
--   components of $A$ implies finiteness of the complement components of
--   $A\cup[a,b]$.  Put
--   $$
--     A_E=V\cup\bigcup_{e\in E} e .
--   $$
--   Then the complement of $A_E$ has only finitely many complement components:
--   there is a finite set of sets whose members are complement components of
--   $A_E$, and every complement component of $A_E$ belongs to that finite set.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `FiniteStraightLineComplexComplementComponents`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FiniteStraightLineComplexComplementComponents.lean#L1-L176

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Baire.Lemmas
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma FiniteStraightLineComplexComplementComponents
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
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
    (hOneEdge :
      ∀ (A : Set (EuclideanSpace ℝ (Fin 2)))
        (V0 : Finset (EuclideanSpace ℝ (Fin 2)))
        (E0 : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
        (a b : EuclideanSpace ℝ (Fin 2)),
        A =
          (V0 : Set (EuclideanSpace ℝ (Fin 2))) ∪
            ⋃ e : {e // e ∈ E0}, segment ℝ e.1.1 e.1.2 →
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E0 → e.1 ∈ V0) →
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E0 → e.2 ∈ V0) →
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E0 → e.1 ≠ e.2) →
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E0 →
            ∀ v : EuclideanSpace ℝ (Fin 2),
              v ∈ V0 → v ∉ openSegment ℝ e.1 e.2) →
        (∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E0 → f ∈ E0 → e ≠ f →
            Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2)) →
        a ∈ V0 → b ∈ V0 → a ≠ b →
        Disjoint (openSegment ℝ a b) A →
        (∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
          (∀ C ∈ comps, ComplementComponent A C) ∧
            ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
              ComplementComponent A C → C ∈ comps) →
        ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
          (∀ C ∈ comps, ComplementComponent (A ∪ segment ℝ a b) C) ∧
            ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
              ComplementComponent (A ∪ segment ℝ a b) C → C ∈ comps) :
    ∃ comps : Finset (Set (EuclideanSpace ℝ (Fin 2))),
      (∀ C ∈ comps,
        ComplementComponent
          ((V : Set (EuclideanSpace ℝ (Fin 2))) ∪
            ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2) C) ∧
        ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
          ComplementComponent
            ((V : Set (EuclideanSpace ℝ (Fin 2))) ∪
              ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2) C →
            C ∈ comps := by sorry
