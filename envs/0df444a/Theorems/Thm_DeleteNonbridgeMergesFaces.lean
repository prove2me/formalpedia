-- Prove2me | Theorems.Thm_DeleteNonbridgeMergesFaces
-- name    : DeleteNonbridgeMergesFaces
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T22:12:31.558298+00:00
-- url     : https://prove2.me/theorems/9cb93b3c-789a-445c-8c75-c384674239b5
-- title:
--   Deleting a non-bridge merges exactly two faces
-- statement:
--   Let $G$ be a finite simple graph with a connected crossing-free ordinary polygonal drawing $D$ and plane-face data $A$. For a non-bridge edge $e$, delete $e$ to form $G_{\mathrm{del}}$. The theorem supplies a crossing-free ordinary polygonal drawing $D_{\mathrm{del}}$ of $G_{\mathrm{del}}$ that keeps the vertex placement and agrees with $D$ on every remaining edge arc, together with plane-face data $A_{\mathrm{del}}$.
--
--   There is a dart $d$ on $e$ whose two incident faces in $A$ are distinct, and a surjective map from the old faces to the new faces such that exactly those two faces are identified. Every other old face is unchanged, the relative interior of $e$ lies in the merged face, and the number of faces decreases by one:
--
--   $$
--   \#\,A_{\mathrm{del}}.\mathrm{Face}+1=\#\,A.\mathrm{Face}.
--   $$
--
--   The edge-arc agreement is stated using the corresponding edge of $G$ for each edge of $G_{\mathrm{del}}$, and the face inclusions and equality clauses are those of the source declaration.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/DeleteNonbridgeMergesFaces.lean#L1-L64

import Definitions.Def_PlaneFaceData
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

-- [TABLET NODE: DeleteNonbridgeMergesFaces]

lemma DeleteNonbridgeMergesFaces {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) (e : G.edgeFinset)
    (hconn : G.Connected) (he : ¬ G.IsBridge e.1) :
    let Gdel : SimpleGraph V := G.deleteEdges {e.1}
    ∃ Ddel : OrdinaryPolygonalDrawing Gdel,
      Ddel.crossingSet.card = 0 ∧
        Ddel.vertexPlacement = D.vertexPlacement ∧
          (∀ ed : Gdel.edgeFinset,
            ∃ eG : G.edgeFinset, eG.1 = ed.1 ∧ eG.1 ≠ e.1 ∧
              Ddel.edgeArc ed = D.edgeArc eG) ∧
            ∃ Adel : PlaneFaceData Gdel Ddel,
              ∃ d : G.Dart,
                d.edge = e.1 ∧
                  A.leftFace d ≠ A.leftFace d.symm ∧
                    ∃ oldToNew : A.Face → Adel.Face,
                      (∀ F : A.Face, A.faceSet F ⊆ Adel.faceSet (oldToNew F)) ∧
                        oldToNew (A.leftFace d) = oldToNew (A.leftFace d.symm) ∧
                          (D.edgeArc e).relativeInterior ⊆
                            Adel.faceSet (oldToNew (A.leftFace d)) ∧
                            (∀ F F' : A.Face,
                              oldToNew F = oldToNew F' ↔
                                F = F' ∨
                                  (F = A.leftFace d ∧ F' = A.leftFace d.symm) ∨
                                    (F = A.leftFace d.symm ∧ F' = A.leftFace d)) ∧
                              (∀ F : A.Face,
                                F ≠ A.leftFace d → F ≠ A.leftFace d.symm →
                                  Adel.faceSet (oldToNew F) = A.faceSet F) ∧
                                (∀ Fdel : Adel.Face, ∃ F : A.Face,
                                  oldToNew F = Fdel) ∧
                                  @Fintype.card Adel.Face Adel.faceFintype + 1 =
                                    @Fintype.card A.Face A.faceFintype := by sorry
