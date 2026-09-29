-- Prove2me | Theorems.Thm_FinalVertexPolygonalScreening
-- name    : FinalVertexPolygonalScreening
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:20:35.764985+00:00
-- url     : https://prove2.me/theorems/a0856f38-2577-43a1-96ad-3b36c4086285
-- title:
--   Final-vertex polygonal screening
-- statement:
--   Given endpoints a and b outside a finite polygonal set K and a nonempty open set W, there is a point x in W outside K for which both segments a--x and x--b satisfy the point-avoidance, non-overlap, and interior transversality conditions relative to every feature of K.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FinalVertexPolygonalScreening.lean#L1-L265

import Definitions.Def_FinitePolygonalSet
open Classical
noncomputable section

lemma FinalVertexPolygonalScreening
    (K : FinitePolygonalSet) (a b : EuclideanSpace ℝ (Fin 2))
    (W : Set (EuclideanSpace ℝ (Fin 2)))
    (ha : a ∉ K.carrier) (hb : b ∉ K.carrier)
    (hWopen : IsOpen W) (hWnonempty : W.Nonempty) :
    ∃ x ∈ W, x ∉ K.carrier ∧
      (∀ p : EuclideanSpace ℝ (Fin 2), p ∈ K.points → p ∉ segment ℝ a x) ∧
      (∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2), s ∈ K.segments →
          ¬ ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
            segment ℝ p q ⊆ segment ℝ a x ∩ segment ℝ s.1 s.2) ∧
      (∀ (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), s ∈ K.segments →
        ∀ p : EuclideanSpace ℝ (Fin 2),
          p ∈ openSegment ℝ a x → p ∈ openSegment ℝ s.1 s.2 →
            ¬ ∃ c : ℝ, s.2 - s.1 = c • (x - a)) ∧
      (∀ p : EuclideanSpace ℝ (Fin 2), p ∈ K.points → p ∉ segment ℝ x b) ∧
      (∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2), s ∈ K.segments →
          ¬ ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
            segment ℝ p q ⊆ segment ℝ x b ∩ segment ℝ s.1 s.2) ∧
      (∀ (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), s ∈ K.segments →
        ∀ p : EuclideanSpace ℝ (Fin 2),
          p ∈ openSegment ℝ x b → p ∈ openSegment ℝ s.1 s.2 →
            ¬ ∃ c : ℝ, s.2 - s.1 = c • (b - x)) := by sorry
