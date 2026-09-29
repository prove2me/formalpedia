-- Prove2me | Theorems.Thm_AdjacentEdgeTailFreeReroute
-- name    : AdjacentEdgeTailFreeReroute
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T21:03:00.507859+00:00
-- url     : https://prove2.me/theorems/5c05a7fe-04e1-4d3a-8afb-22a2a2b680e8
-- title:
--   The tail-free strict-reduction primitive
-- statement:
--   This is the tail-free strict-reduction primitive for ordinary polygonal drawings.
--
--   Let $G$ be a finite simple graph, let $D$ be an ordinary polygonal drawing of $G$, and let $\alpha$ and $\beta$ be distinct edges incident with a common vertex $u$. If some point $x$ of the crossing set of $D$ lies in the relative interior of both drawn edges, then there exists an ordinary polygonal drawing $D'$ of $G$ with strictly fewer crossings:
--
--   $$\lvert\operatorname{Cross}(D')\rvert < \lvert\operatorname{Cross}(D)\rvert.$$
--
--   This is the local strict-improvement step used to eliminate crossings between adjacent edges in a crossing-minimal drawing.
--
--   **Formalization Note** The Lean statement records the common incidence by membership of $u$ in the endpoint pairs of the two edge-finsets, and records the crossing point explicitly as a member of `D.crossingSet` and of both edge relative interiors.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/AdjacentEdgeTailFreeReroute.lean#L1-L24

import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

lemma AdjacentEdgeTailFreeReroute {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (alpha beta : G.edgeFinset) (u : V) :
    alpha ≠ beta →
      u ∈ alpha.1 →
        u ∈ beta.1 →
          (∃ x : EuclideanSpace ℝ (Fin 2),
            x ∈ D.crossingSet ∧
              x ∈ (D.edgeArc alpha).relativeInterior ∧
                x ∈ (D.edgeArc beta).relativeInterior) →
            ∃ D' : OrdinaryPolygonalDrawing G,
              D'.crossingSet.card < D.crossingSet.card := by sorry
