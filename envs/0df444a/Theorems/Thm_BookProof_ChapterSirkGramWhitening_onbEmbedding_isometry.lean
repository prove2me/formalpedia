-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_onbEmbedding_isometry
-- name    : BookProof.ChapterSirkGramWhitening.onbEmbedding_isometry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:53:36.460138+00:00
-- url     : https://prove2.me/theorems/00334a39-084f-4658-b33e-389f592cede8
-- title:
--   {d : ℕ} (S : Submodule ℂ E) [CompleteSpace S] (b : OrthonormalBasis (Fin d) ℂ S) : (ContinuousLinearMap.adjoint (onbEmbedding S b)).comp (onbEmbedding S b) = ContinuousLinearMap.id ℂ...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.onbEmbedding_isometry` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.onbEmbedding_isometry
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.onbEmbedding_isometry {d : ℕ} (S : Submodule ℂ E) [CompleteSpace S]
    (b : OrthonormalBasis (Fin d) ℂ S) :
    (ContinuousLinearMap.adjoint (onbEmbedding S b)).comp (onbEmbedding S b)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)) := by sorry
