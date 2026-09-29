-- Prove2me | Theorems.Thm_BookProof_ChapterH9_convexHull_numRange_compress_mono
-- name    : BookProof.ChapterH9.convexHull_numRange_compress_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:21:47.026587+00:00
-- url     : https://prove2.me/theorems/8f7b6dd2-c606-4d2f-92a7-bae7a5b20031
-- title:
--   The Lean 4 theorem `convexHull_numRange_compress_mono` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `convexHull_numRange_compress_mono` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.convexHull_numRange_compress_mono
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

theorem BookProof.ChapterH9.convexHull_numRange_compress_mono (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E)
    (J : F →L[ℂ] G) (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) (hJiso : ∀ x : F, ‖J x‖ = ‖x‖) :
    convexHull ℝ (numRange (compress Vn X)) ⊆ convexHull ℝ (numRange (compress Vm X)) := by sorry
