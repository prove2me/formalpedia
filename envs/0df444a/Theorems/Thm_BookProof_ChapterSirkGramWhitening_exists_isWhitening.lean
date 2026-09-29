-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_exists_isWhitening
-- name    : BookProof.ChapterSirkGramWhitening.exists_isWhitening
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:58:34.485712+00:00
-- url     : https://prove2.me/theorems/b03b05e6-227c-4c73-8e17-e65b870c1c90
-- title:
--   {m : ℕ} {w : Fin m → E} (hw : LinearIndependent ℂ w) : ∃ T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m), Function.Bijective T ∧ IsWhitening w T
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.exists_isWhitening` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.exists_isWhitening
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.exists_isWhitening {m : ℕ} {w : Fin m → E} (hw : LinearIndependent ℂ w) :
    ∃ T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m),
      Function.Bijective T ∧ IsWhitening w T := by sorry
