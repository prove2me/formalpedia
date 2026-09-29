-- Prove2me | Theorems.Thm_DartSuccessorPreservesFace
-- name    : DartSuccessorPreservesFace
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T21:56:31.521144+00:00
-- url     : https://prove2.me/theorems/4d7dfa4d-6311-4353-b89a-e37bb46da711
-- title:
--   Dart successor preserves the left face
-- statement:
--   For a crossing-free ordinary polygonal drawing equipped with plane face data, the successor permutation preserves the face on the left of every dart. Consequently, if a dart has left face $F$, then every forward and backward iterate of the successor permutation also has left face $F$; the darts incident with any fixed face are unions of successor orbits.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/DartSuccessorPreservesFace.lean#L1-L13

import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma DartSuccessorPreservesFace {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    (∀ d : G.Dart, A.leftFace (A.successor d) = A.leftFace d) ∧
      ∀ F : A.Face, ∀ d : G.Dart, A.leftFace d = F →
        (∀ n : ℕ, A.leftFace ((A.successor^[n]) d) = F) ∧
          ∀ n : ℕ, A.leftFace (((A.successor.symm)^[n]) d) = F := by sorry
