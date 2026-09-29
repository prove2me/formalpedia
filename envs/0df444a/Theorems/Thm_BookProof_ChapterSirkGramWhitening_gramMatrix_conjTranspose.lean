-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_gramMatrix_conjTranspose
-- name    : BookProof.ChapterSirkGramWhitening.gramMatrix_conjTranspose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:24:03.106849+00:00
-- url     : https://prove2.me/theorems/6836026d-58db-4c12-9b01-189c4bddcba4
-- title:
--   {m : ℕ} (w : Fin m → E) : (gramMatrix w)ᴴ = gramMatrix w
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.gramMatrix_conjTranspose` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.gramMatrix_conjTranspose
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.gramMatrix_conjTranspose {m : ℕ} (w : Fin m → E) :
    (gramMatrix w)ᴴ = gramMatrix w := by sorry
