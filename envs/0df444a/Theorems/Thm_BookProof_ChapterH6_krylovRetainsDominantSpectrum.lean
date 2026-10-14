-- Prove2me | Theorems.Thm_BookProof_ChapterH6_krylovRetainsDominantSpectrum
-- name    : BookProof.ChapterH6.krylovRetainsDominantSpectrum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T16:44:01.060987+00:00
-- url     : https://prove2.me/theorems/342786ef-e581-4415-9342-d27af726aeb4
-- title:
--   The Lean 4 theorem `krylovRetainsDominantSpectrum` in the `ChapterH6` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `krylovRetainsDominantSpectrum` in the `ChapterH6` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH6.lean

-- Generated from ChapterH6.lean — theorem BookProof.ChapterH6.krylovRetainsDominantSpectrum
import Mathlib
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH4
open BookProof.ChapterH4
open BookProof.ChapterH6


noncomputable section

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterH6.krylovRetainsDominantSpectrum (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (lam : ℂ) (y : F) (hy : ‖y‖ = 1)
    (heig : compress V X y = lam • y) :
    lam = inner ℂ (V y) (X (V y)) ∧ ‖lam‖ ≤ ‖X‖ := by sorry
