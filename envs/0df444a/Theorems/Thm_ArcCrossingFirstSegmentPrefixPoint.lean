-- Prove2me | Theorems.Thm_ArcCrossingFirstSegmentPrefixPoint
-- name    : ArcCrossingFirstSegmentPrefixPoint
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T21:39:20.445686+00:00
-- url     : https://prove2.me/theorems/39c5d479-0398-484b-9213-0840249699a0
-- title:
--   Clear prefix point on the first crossing segment
-- statement:
--   For a finite path--arc intersection and a segment whose endpoints avoid the path, there is a point \(c\) on that segment, distinct from both endpoints and outside the path, such that the prefix from the left endpoint to \(c\) is contained in the segment and avoids the path. This isolates the first crossing from the earlier part of the arc.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingFirstSegmentPrefixPoint.lean#L1-116

import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingFirstSegmentPrefixPoint
    (δ : PolygonalArc) (α : PolygonalPath) (j : ℕ)
    (hj : j + 1 < δ.vertices.length) :
    Set.Finite (α.carrier ∩ δ.carrier) →
      (α.carrier ∩ segment ℝ δ.vertices[j] δ.vertices[j + 1]).Nonempty →
        δ.vertices[j] ∉ α.carrier →
          δ.vertices[j + 1] ∉ α.carrier →
            ∃ c : EuclideanSpace ℝ (Fin 2),
              c ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] ∧
                c ≠ δ.vertices[j] ∧
                  c ≠ δ.vertices[j + 1] ∧
                    c ∉ α.carrier ∧
                      segment ℝ δ.vertices[j] c ⊆
                        segment ℝ δ.vertices[j] δ.vertices[j + 1] ∩ α.carrierᶜ := by sorry
