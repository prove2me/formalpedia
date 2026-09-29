-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_selfAdjoint_re_inner_coe
-- name    : BookProof.ChapterSirkRitzSpectrum.selfAdjoint_re_inner_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:30:55.293222+00:00
-- url     : https://prove2.me/theorems/f12e3e0a-ee27-480c-a148-f502c1efd302
-- title:
--   (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (x : F) : (((inner ℂ (T x) x : ℂ).re : ℝ) : ℂ) = inner ℂ (T x) x
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.selfAdjoint_re_inner_coe` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.selfAdjoint_re_inner_coe
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.selfAdjoint_re_inner_coe (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (x : F) :
    (((inner ℂ (T x) x : ℂ).re : ℝ) : ℂ) = inner ℂ (T x) x := by sorry
