-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_onbEmbedding_apply
-- name    : BookProof.ChapterSirkGramWhitening.onbEmbedding_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:27:08.214325+00:00
-- url     : https://prove2.me/theorems/265f45fe-d6eb-49c8-b08d-67406b40e7b9
-- title:
--   {d : ℕ} (S : Submodule ℂ E) [CompleteSpace S] (b : OrthonormalBasis (Fin d) ℂ S) (c : EuclideanSpace ℂ (Fin d)) : onbEmbedding S b c = (b.repr.symm c : E)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.onbEmbedding_apply` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.onbEmbedding_apply
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.onbEmbedding_apply {d : ℕ} (S : Submodule ℂ E) [CompleteSpace S]
    (b : OrthonormalBasis (Fin d) ℂ S) (c : EuclideanSpace ℂ (Fin d)) :
    onbEmbedding S b c = (b.repr.symm c : E) := by sorry
