-- Prove2me | Theorems.Thm_ArcCrossingOldPrefixDisjointTail
-- name    : ArcCrossingOldPrefixDisjointTail
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:17:58.534312+00:00
-- url     : https://prove2.me/theorems/fac6500b-0dd4-4005-92e8-cda6ce115ed3
-- title:
--   Old-prefix disjointness from the ordered crossing tail
-- statement:
--   Let $\delta$ and $	au$ be polygonal arcs, let $j$ index an edge of $\delta$, let $c$ lie in the open edge from $\delta_j$ to $\delta_{j+1}$, and let $d$ lie strictly between $\delta_j$ and $c$. If $	au$ starts at $c$ and then follows the tail of $\delta$ after that edge, then the earlier prefix of $\delta$ together with the segment from $\delta_j$ to $d$ is disjoint from the carrier of $	au$.
--
--   This is the geometric separation statement that isolates the old prefix from the ordered tail in the source-prefix construction.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingOldPrefixDisjointTail.lean#L1-280

import Definitions.Def_ArcCrossingEarlierPrefix
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma ArcCrossingOldPrefixDisjointTail
    (δ τ : PolygonalArc) (j : ℕ) (c d : EuclideanSpace ℝ (Fin 2))
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hdOpen : d ∈ openSegment ℝ δ.vertices[j] c)
    (hτvertices : τ.vertices = c :: δ.vertices.drop (j + 1)) :
    Disjoint
      (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)
      τ.carrier := by sorry
