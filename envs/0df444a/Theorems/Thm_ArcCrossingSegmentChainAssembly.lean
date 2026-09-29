-- Prove2me | Theorems.Thm_ArcCrossingSegmentChainAssembly
-- name    : ArcCrossingSegmentChainAssembly
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:55:35.710119+00:00
-- url     : https://prove2.me/theorems/2325c2e1-d2e2-4a15-b614-387baf7b613f
-- title:
--   Arc-crossing segment chain assembly
-- statement:
--   A list of vertices with a polygonal path piece between each consecutive pair can be assembled into a finite ordered list of polygonal paths with matching endpoints and a common carrier containment set.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingSegmentChainAssembly.lean#L1-L101

import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingSegmentChainAssembly
    (V : List (EuclideanSpace ℝ (Fin 2)))
    (source target : EuclideanSpace ℝ (Fin 2))
    (S : Set (EuclideanSpace ℝ (Fin 2))) :
    V.head? = some source →
      V.getLast? = some target →
        1 < V.length →
          (∀ (i : ℕ) (hi : i + 1 < V.length),
            ∃ η : PolygonalPath,
              η.source = V[i] ∧
                η.target = V[i + 1] ∧
                  η.carrier ⊆ S) →
            ∃ (pieces : List PolygonalPath) (first last : PolygonalPath),
              pieces.head? = some first ∧
                pieces.getLast? = some last ∧
                  first.source = source ∧
                    last.target = target ∧
                      (∀ η : PolygonalPath, η ∈ pieces → η.carrier ⊆ S) ∧
                        (∀ (i : ℕ) (hi : i + 1 < pieces.length),
                          (pieces[i]).target = (pieces[i + 1]).source) := by sorry
