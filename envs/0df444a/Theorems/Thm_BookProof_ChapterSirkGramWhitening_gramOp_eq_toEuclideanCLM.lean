-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_gramOp_eq_toEuclideanCLM
-- name    : BookProof.ChapterSirkGramWhitening.gramOp_eq_toEuclideanCLM
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:57:50.629052+00:00
-- url     : https://prove2.me/theorems/de582c92-87e2-480a-927d-27248fa270e3
-- title:
--   {m : ℕ} (w : Fin m → E) : gramOp w = Matrix.toEuclideanCLM (𝕜
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.gramOp_eq_toEuclideanCLM` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.gramOp_eq_toEuclideanCLM
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.gramOp_eq_toEuclideanCLM {m : ℕ} (w : Fin m → E) :
    gramOp w = Matrix.toEuclideanCLM (𝕜 := ℂ) (gramMatrix w) := by sorry
