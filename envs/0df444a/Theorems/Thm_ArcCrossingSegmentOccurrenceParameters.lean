-- Prove2me | Theorems.Thm_ArcCrossingSegmentOccurrenceParameters
-- name    : ArcCrossingSegmentOccurrenceParameters
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:55:25.526131+00:00
-- url     : https://prove2.me/theorems/11c9b1ec-9f24-4e36-9bbf-c609900d80c8
-- title:
--   Arc-crossing segment occurrence parameters
-- statement:
--   For a fixed segment of a polygonal path, the finite intersections with a polygonal arc admit a finite, strictly ordered list of affine parameters in the open unit interval, representing exactly the intersection points and leaving no intersection parameter between consecutive entries.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingSegmentOccurrenceParameters.lean#L1-L141

import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingSegmentOccurrenceParameters
    (γ : PolygonalArc) (α : PolygonalPath)
    (i : ℕ) (hi : i + 1 < α.vertices.length) :
    Set.Finite (α.carrier ∩ γ.carrier) →
      (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ α.vertices → v ∉ γ.carrier) →
        ∃ params : List ℝ,
          params.Nodup ∧
            params.SortedLT ∧
              (∀ t : ℝ, t ∈ params ↔
                AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∈
                  openSegment ℝ α.vertices[i] α.vertices[i + 1] ∩ γ.carrier) ∧
                (∀ t : ℝ, t ∈ params → 0 < t ∧ t < 1) ∧
                  (∀ x : EuclideanSpace ℝ (Fin 2),
                    x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                      x ∈ γ.carrier →
                        ∃ t : ℝ,
                          t ∈ params ∧ 0 < t ∧ t < 1 ∧
                            AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t = x) ∧
                    (∀ n (hn : n + 1 < params.length), params[n] < params[n + 1]) ∧
                      (∀ n (hn : n + 1 < params.length) t,
                        0 < t → t < 1 →
                          AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∈
                            γ.carrier →
                            ¬ (params[n] < t ∧ t < params[n + 1])) := by sorry
