-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_norm_whitened_apply
-- name    : BookProof.ChapterSirkGramWhitening.norm_whitened_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:51:18.509245+00:00
-- url     : https://prove2.me/theorems/36de1446-646a-4d4e-95e4-befa2ab547e8
-- title:
--   {m : ℕ} (w : Fin m → E) {T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)} (hT : IsWhitening w T) (c : EuclideanSpace ℂ (Fin m)) : ‖whitened w T c‖ = ‖c‖
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.norm_whitened_apply` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.norm_whitened_apply
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.norm_whitened_apply {m : ℕ} (w : Fin m → E)
    {T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)} (hT : IsWhitening w T)
    (c : EuclideanSpace ℂ (Fin m)) : ‖whitened w T c‖ = ‖c‖ := by sorry
