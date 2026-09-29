-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_synthesis_mem_span
-- name    : BookProof.ChapterSirkGramWhitening.synthesis_mem_span
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:50:37.001209+00:00
-- url     : https://prove2.me/theorems/d83f3d3f-e9cf-432f-9629-eeaf0d5176c6
-- title:
--   {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) : synthesis w c ∈ Submodule.span ℂ (Set.range w)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.synthesis_mem_span` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.synthesis_mem_span
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.synthesis_mem_span {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) :
    synthesis w c ∈ Submodule.span ℂ (Set.range w) := by sorry
