-- Prove2me | Theorems.Thm_FaceDegreeLowerBound
-- name    : FaceDegreeLowerBound
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T21:35:52.842327+00:00
-- url     : https://prove2.me/theorems/99dfbbbc-1ef5-4048-b624-96de30c8bc07
-- title:
--   Lower bound on the degree of every plane face
-- statement:
--   For a connected graph with at least three vertices and at least one edge, every face in its crossing-free plane face data has boundary degree at least three.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/FaceDegreeLowerBound.lean#L1-L135

import Definitions.Def_PlaneFaceData
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Classical
noncomputable section

lemma FaceDegreeLowerBound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.Connected → 3 ≤ Fintype.card V → 0 < G.edgeFinset.card →
      ∀ F : A.Face, 3 ≤ A.faceDegree F := by sorry
