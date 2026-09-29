-- Prove2me | Theorems.Thm_BookProof_ChapterH9_mem_numRange
-- name    : BookProof.ChapterH9.mem_numRange
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:35:16.013814+00:00
-- url     : https://prove2.me/theorems/c4c722e5-4272-4deb-92d7-bd151c8197c0
-- title:
--   The Lean 4 theorem `mem_numRange` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mem_numRange` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.mem_numRange
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

theorem BookProof.ChapterH9.mem_numRange {X : E →L[ℂ] E} (x : E) (hx : ‖x‖ = 1) :
    (inner ℂ x (X x) : ℂ) ∈ numRange X := by sorry
