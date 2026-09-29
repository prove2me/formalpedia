-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_range_onbEmbedding
-- name    : BookProof.ChapterSirkGramWhitening.range_onbEmbedding
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:27:46.056235+00:00
-- url     : https://prove2.me/theorems/04604756-ef6d-4529-a2dd-0eb497e39692
-- title:
--   {d : ℕ} (S : Submodule ℂ E) [CompleteSpace S] (b : OrthonormalBasis (Fin d) ℂ S) : LinearMap.range (onbEmbedding S b : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E) = S
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.range_onbEmbedding` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.range_onbEmbedding
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.range_onbEmbedding {d : ℕ} (S : Submodule ℂ E) [CompleteSpace S]
    (b : OrthonormalBasis (Fin d) ℂ S) :
    LinearMap.range (onbEmbedding S b : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E) = S := by sorry
