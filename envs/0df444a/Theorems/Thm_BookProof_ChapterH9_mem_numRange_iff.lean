-- Prove2me | Theorems.Thm_BookProof_ChapterH9_mem_numRange_iff
-- name    : BookProof.ChapterH9.mem_numRange_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:35:41.255443+00:00
-- url     : https://prove2.me/theorems/9504a169-bd9a-4f25-bf8b-0530ea9eacd0
-- title:
--   The Lean 4 theorem `mem_numRange_iff` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mem_numRange_iff` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.mem_numRange_iff
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

theorem BookProof.ChapterH9.mem_numRange_iff {X : E →L[ℂ] E} {c : ℂ} :
    c ∈ numRange X ↔ ∃ x : E, ‖x‖ = 1 ∧ (inner ℂ x (X x) : ℂ) = c := by sorry
