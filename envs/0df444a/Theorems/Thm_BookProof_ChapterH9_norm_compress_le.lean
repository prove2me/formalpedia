-- Prove2me | Theorems.Thm_BookProof_ChapterH9_norm_compress_le
-- name    : BookProof.ChapterH9.norm_compress_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:22:10.561385+00:00
-- url     : https://prove2.me/theorems/50ffb74d-f7c5-45e8-883a-423908ed5f1b
-- title:
--   The Lean 4 theorem `norm_compress_le` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_compress_le` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.norm_compress_le
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

theorem BookProof.ChapterH9.norm_compress_le (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) :
    ‖compress V X‖ ≤ ‖X‖ := by sorry
