-- Prove2me | Theorems.Thm_ArcCrossingSegmentOrderedWindowParameters
-- name    : ArcCrossingSegmentOrderedWindowParameters
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:55:41.070156+00:00
-- url     : https://prove2.me/theorems/73592294-8b09-479d-beb0-2d131ca67222
-- title:
--   Arc-crossing ordered window parameters
-- statement:
--   Given ordered intersection parameters and a pair of enclosing affine parameters for each occurrence, pairwise disjoint detour windows can be chosen while preserving the endpoint representations and the order of the windows.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ArcCrossingSegmentOrderedWindowParameters.lean#L1-L115

import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingSegmentOrderedWindowParameters
    (α : PolygonalPath) (i : ℕ) (hi : i + 1 < α.vertices.length)
    (cutBefore cutAfter :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (params : List ℝ) :
    (∀ n (hn : n < params.length),
      ∃ b a : ℝ,
        0 < b ∧ b < params[n] ∧ params[n] < a ∧ a < 1 ∧
          AffineMap.lineMap α.vertices[i] α.vertices[i + 1] b =
            cutBefore (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n]) ∧
            AffineMap.lineMap α.vertices[i] α.vertices[i + 1] a =
              cutAfter (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n])) →
      (∀ n (hn : n + 1 < params.length), params[n] < params[n + 1]) →
        (∀ n (hn : n + 1 < params.length),
          Disjoint
            (segment ℝ
              (cutBefore (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n]))
              (cutAfter (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n])))
            (segment ℝ
              (cutBefore
                (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n + 1]))
              (cutAfter
                (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n + 1])))) →
          ∃ left right : (n : ℕ) → n < params.length → ℝ,
            (∀ n (hn : n < params.length),
              0 < left n hn ∧ left n hn < params[n] ∧
                params[n] < right n hn ∧ right n hn < 1 ∧
                  AffineMap.lineMap α.vertices[i] α.vertices[i + 1] (left n hn) =
                    cutBefore
                      (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n]) ∧
                    AffineMap.lineMap α.vertices[i] α.vertices[i + 1] (right n hn) =
                      cutAfter
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n])) ∧
              (∀ n (hn : n + 1 < params.length),
                right n (Nat.lt_of_succ_lt hn) < left (n + 1) hn) := by sorry
