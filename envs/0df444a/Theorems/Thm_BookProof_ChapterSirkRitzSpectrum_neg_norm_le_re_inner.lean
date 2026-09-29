-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_neg_norm_le_re_inner
-- name    : BookProof.ChapterSirkRitzSpectrum.neg_norm_le_re_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:41:06.196177+00:00
-- url     : https://prove2.me/theorems/9c1f0af6-109d-489e-a4cf-5f1d31a1d901
-- title:
--   (T : F →L[ℂ] F) (x : F) : -(‖T‖ * ‖x‖ ^ 2) ≤ (inner ℂ x (T x) : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.neg_norm_le_re_inner` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.neg_norm_le_re_inner
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.neg_norm_le_re_inner (T : F →L[ℂ] F) (x : F) :
    -(‖T‖ * ‖x‖ ^ 2) ≤ (inner ℂ x (T x) : ℂ).re := by sorry
