-- Prove2me | Theorems.Thm_ArcCrossingInitialConeAvoidsBackwardGerm
-- name    : ArcCrossingInitialConeAvoidsBackwardGerm
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:54:29.731842+00:00
-- url     : https://prove2.me/theorems/76e8dbe8-35ba-4650-b2d0-07ca38f12a81
-- title:
--   ArcCrossingInitialConeAvoidsBackwardGerm
-- statement:
--   For an oriented tail whose first vertex is an interior point of a polygonal-arc edge, the initial endpoint cone is disjoint from the backward segment from that interior point to the preceding vertex. This prevents the initial cone from meeting the already traversed germ.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingInitialConeAvoidsBackwardGerm.lean#L1-107

import Definitions.Def_PolygonalArcInitialEndpointCone
import Definitions.Def_PolygonalArc

import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor

open Classical
noncomputable section

lemma ArcCrossingInitialConeAvoidsBackwardGerm
    (δ τ : PolygonalArc) (j : ℕ) (c : EuclideanSpace ℝ (Fin 2))
    (r K₀ : ℝ)
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hτvertices : τ.vertices = c :: δ.vertices.drop (j + 1))
    (hτsource : τ.source = c) :
    Disjoint (PolygonalArcInitialEndpointCone τ r K₀) (segment ℝ c δ.vertices[j]) := by sorry
