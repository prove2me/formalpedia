-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_spectrum_real_bddBelow
-- name    : BookProof.ChapterSirkRitzSpectrum.spectrum_real_bddBelow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:45:35.176155+00:00
-- url     : https://prove2.me/theorems/a12f5065-36f9-4963-ac3a-2c2fe283909b
-- title:
--   (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) : BddBelow (spectrum ℝ T)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.spectrum_real_bddBelow` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.spectrum_real_bddBelow
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.spectrum_real_bddBelow (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) :
    BddBelow (spectrum ℝ T) := by sorry
