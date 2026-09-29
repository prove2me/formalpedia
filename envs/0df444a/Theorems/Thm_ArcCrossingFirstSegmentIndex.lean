-- Prove2me | Theorems.Thm_ArcCrossingFirstSegmentIndex
-- name    : ArcCrossingFirstSegmentIndex
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T21:39:11.125962+00:00
-- url     : https://prove2.me/theorems/a9365e49-e59a-4649-8004-20542d6fd9ee
-- title:
--   First polygonal-arc segment meeting a path
-- statement:
--   If a path meets a polygonal arc, some arc segment meets the path. The theorem selects the least such index \(j\), records the nonempty intersection with that segment, proves that every later meeting segment has index at least \(j\), and shows that all earlier segments are disjoint from the path.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingFirstSegmentIndex.lean#L1-38

import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingFirstSegmentIndex
    (δ : PolygonalArc) (α : PolygonalPath) :
    (α.carrier ∩ δ.carrier).Nonempty →
      ∃ j : ℕ, ∃ hj : j + 1 < δ.vertices.length,
        (α.carrier ∩ segment ℝ δ.vertices[j] δ.vertices[j + 1]).Nonempty ∧
          (∀ (i : ℕ) (hi : i + 1 < δ.vertices.length),
            (α.carrier ∩ segment ℝ δ.vertices[i] δ.vertices[i + 1]).Nonempty →
              j ≤ i) ∧
            (∀ (i : ℕ) (hi : i + 1 < δ.vertices.length),
              i < j → Disjoint α.carrier (segment ℝ δ.vertices[i] δ.vertices[i + 1])) := by sorry
