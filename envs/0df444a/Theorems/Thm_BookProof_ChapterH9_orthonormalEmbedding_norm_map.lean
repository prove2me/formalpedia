-- Prove2me | Theorems.Thm_BookProof_ChapterH9_orthonormalEmbedding_norm_map
-- name    : BookProof.ChapterH9.orthonormalEmbedding_norm_map
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:20:49.425242+00:00
-- url     : https://prove2.me/theorems/e7bbdfb1-2f5f-4a8e-a736-ea10e194ec8c
-- title:
--   The Lean 4 theorem `orthonormalEmbedding_norm_map` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `orthonormalEmbedding_norm_map` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.orthonormalEmbedding_norm_map
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

theorem BookProof.ChapterH9.orthonormalEmbedding_norm_map {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w)
    (x : EuclideanSpace ℂ (Fin m)) : ‖orthonormalEmbedding w hw x‖ = ‖x‖ := by sorry
