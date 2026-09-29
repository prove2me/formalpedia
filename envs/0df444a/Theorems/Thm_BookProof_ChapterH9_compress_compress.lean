-- Prove2me | Theorems.Thm_BookProof_ChapterH9_compress_compress
-- name    : BookProof.ChapterH9.compress_compress
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:34:26.092516+00:00
-- url     : https://prove2.me/theorems/afd7975c-b12b-4389-a23c-a7dad7a281ea
-- title:
--   The Lean 4 theorem `compress_compress` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `compress_compress` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.compress_compress
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

theorem BookProof.ChapterH9.compress_compress (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) :
    compress Vn X = compress J (compress Vm X) := by sorry
