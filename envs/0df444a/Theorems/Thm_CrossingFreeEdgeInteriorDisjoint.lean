-- Prove2me | Theorems.Thm_CrossingFreeEdgeInteriorDisjoint
-- name    : CrossingFreeEdgeInteriorDisjoint
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T19:36:18.322861+00:00
-- url     : https://prove2.me/theorems/4810d1aa-9570-4059-b22e-02ff0e5fd923
-- title:
--   Distinct edge interiors are disjoint in a crossing-free drawing
-- statement:
--   Let $G$ be a finite simple graph equipped with an ordinary polygonal drawing $D$. If the drawing has no crossing points, then the relative interiors of any two distinct drawn edges are disjoint. In other words, for distinct edges $e_1$ and $e_2$ and any point $p$,
--
--   $$
--    e_1\ne e_2 \quad\Longrightarrow\quad p\in\operatorname{relint}(D(e_1))\ \text{and}\ p\in\operatorname{relint}(D(e_2))\ \text{is impossible}.
--   $$
--
--   This is the basic crossing-free separation fact used when analyzing how a pendant edge can meet the remainder of a planar drawing.
--
--   **Formalization Note** The drawing's crossing set is a finite set of points, and the hypothesis that its cardinality is zero expresses that it is empty.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/CrossingFreeEdgeInteriorDisjoint.lean#L1-L22

import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

lemma CrossingFreeEdgeInteriorDisjoint {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0) :
    ∀ ⦃e₁ e₂ : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e₁ ≠ e₂ →
        p ∈ (D.edgeArc e₁).relativeInterior →
          p ∈ (D.edgeArc e₂).relativeInterior → False := by sorry
