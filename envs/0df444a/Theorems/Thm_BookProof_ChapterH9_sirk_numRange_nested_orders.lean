-- Prove2me | Theorems.Thm_BookProof_ChapterH9_sirk_numRange_nested_orders
-- name    : BookProof.ChapterH9.sirk_numRange_nested_orders
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:23:31.584986+00:00
-- url     : https://prove2.me/theorems/b034800b-0f20-46d4-8370-84c8776ad54f
-- title:
--   The Lean 4 theorem `sirk_numRange_nested_orders` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_numRange_nested_orders` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.sirk_numRange_nested_orders
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9


noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterH9.sirk_numRange_nested_orders {m n : ℕ} (hmn : m ≤ n) (X : E →L[ℂ] E)
    (w : Fin m → E) (w' : Fin n → E) (hw : Orthonormal ℂ w) (hw' : Orthonormal ℂ w')
    (hnest : ∀ i : Fin m, w i = w' (Fin.castLE hmn i)) :
    numRange (compress (orthonormalEmbedding w hw) X)
        ⊆ numRange (compress (orthonormalEmbedding w' hw') X)
      ∧ numRange (compress (orthonormalEmbedding w' hw') X) ⊆ numRange X
      ∧ numRange X ⊆ Metric.closedBall (0 : ℂ) ‖X‖
      ∧ ‖compress (orthonormalEmbedding w hw) X‖
          ≤ ‖compress (orthonormalEmbedding w' hw') X‖
      ∧ ‖compress (orthonormalEmbedding w' hw') X‖ ≤ ‖X‖ := by sorry
