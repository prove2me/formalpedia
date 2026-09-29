-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_inner_synthesis_left
-- name    : BookProof.ChapterSirkGramWhitening.inner_synthesis_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:25:54.918179+00:00
-- url     : https://prove2.me/theorems/f90ceafa-4e87-4043-b398-62efebec877d
-- title:
--   {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) (x : E) : ⟪synthesis w c, x⟫_ℂ = ∑ i, (starRingEnd ℂ) (c i) * ⟪w i, x⟫_ℂ
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.inner_synthesis_left` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.inner_synthesis_left
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.inner_synthesis_left {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) (x : E) :
    ⟪synthesis w c, x⟫_ℂ = ∑ i, (starRingEnd ℂ) (c i) * ⟪w i, x⟫_ℂ := by sorry
