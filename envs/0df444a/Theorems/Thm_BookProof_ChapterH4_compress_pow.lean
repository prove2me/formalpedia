-- Prove2me | Theorems.Thm_BookProof_ChapterH4_compress_pow
-- name    : BookProof.ChapterH4.compress_pow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:38:49.659067+00:00
-- url     : https://prove2.me/theorems/dbcc2231-82fc-4e50-9e52-2bb5900cc83f
-- title:
--   (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (hinv : ∀ x : F, ∃ y : F, X (V x) = V y) (n : ℕ) : (X ^ n).comp V = V.comp ((compress V X) ^ n)
-- statement:
--   Lean 4 theorem `BookProof.ChapterH4.compress_pow` (module `BookProof.ChapterH4`), source chapter `BookProof/ChapterChapterH4.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH4.lean

-- Generated from ChapterH4.lean — theorem BookProof.ChapterH4.compress_pow
import Mathlib
import Definitions.Def_ChapterH4
open BookProof.ChapterH4









open scoped BigOperators


noncomputable section





variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterH4.compress_pow (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hinv : ∀ x : F, ∃ y : F, X (V x) = V y) (n : ℕ) :
    (X ^ n).comp V = V.comp ((compress V X) ^ n) := by sorry
