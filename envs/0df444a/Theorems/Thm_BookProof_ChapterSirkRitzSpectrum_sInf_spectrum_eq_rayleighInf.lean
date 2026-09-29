-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_sInf_spectrum_eq_rayleighInf
-- name    : BookProof.ChapterSirkRitzSpectrum.sInf_spectrum_eq_rayleighInf
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:48:11.54429+00:00
-- url     : https://prove2.me/theorems/500291f4-7e39-4007-bd00-c95df6cbca9c
-- title:
--   [Nontrivial F] (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) : sInf (spectrum ℝ T) = rayleighInf T
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.sInf_spectrum_eq_rayleighInf` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.sInf_spectrum_eq_rayleighInf
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.sInf_spectrum_eq_rayleighInf [Nontrivial F] (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) :
    sInf (spectrum ℝ T) = rayleighInf T := by sorry
