-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_spectrum_real_nonempty
-- name    : BookProof.ChapterSirkRitzSpectrum.spectrum_real_nonempty
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:46:12.260828+00:00
-- url     : https://prove2.me/theorems/ab13b2aa-2ed8-4cef-be59-4da844813ec6
-- title:
--   [Nontrivial F] (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) : (spectrum ℝ T).Nonempty
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.spectrum_real_nonempty` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.spectrum_real_nonempty
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.spectrum_real_nonempty [Nontrivial F] (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) :
    (spectrum ℝ T).Nonempty := by sorry
