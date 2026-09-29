-- Prove2me | Theorems.Thm_ArcCrossingOrderedTailArc
-- name    : ArcCrossingOrderedTailArc
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T21:39:17.318388+00:00
-- url     : https://prove2.me/theorems/f927ab19-a202-49e2-a9ae-fc7349692bd5
-- title:
--   Ordered tail arc after the first crossing
-- statement:
--   Starting at an interior point \(c\) of the first crossing segment, the theorem forms the polygonal tail \(\tau\) consisting of \(c\) followed by the remaining vertices. The tail remains inside the original arc, contains every path--arc intersection in its relative interior, and is disjoint from the endpoint-attached compact set \(K\).
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingOrderedTailArc.lean#L1-591

import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalPath

open Classical
noncomputable section

set_option maxHeartbeats 1000000

lemma ArcCrossingOrderedTailArc
    (K : Set (EuclideanSpace ℝ (Fin 2))) (δ : PolygonalArc)
    (α : PolygonalPath) (j : ℕ) (c : EuclideanSpace ℝ (Fin 2))
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hc_notα : c ∉ α.carrier)
    (hbefore :
      ∀ (i : ℕ) (hi : i + 1 < δ.vertices.length),
        i < j → Disjoint α.carrier (segment ℝ δ.vertices[i] δ.vertices[i + 1]))
    (hprefix_disjoint : Disjoint (segment ℝ δ.vertices[j] c) α.carrier)
    (hδverticesAvoid :
      ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ δ.vertices → v ∉ α.carrier)
    (hδK :
      δ.carrier ∩ K = ({δ.source} : Set (EuclideanSpace ℝ (Fin 2)))) :
    ∃ τ : PolygonalArc,
      τ.vertices = c :: δ.vertices.drop (j + 1) ∧
        τ.source = c ∧
          τ.target = δ.target ∧
            τ.carrier ⊆ δ.carrier ∧
              α.carrier ∩ δ.carrier ⊆ τ.relativeInterior ∧
                Disjoint τ.carrier K := by sorry
