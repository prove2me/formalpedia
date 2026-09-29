-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_abs_re_inner_le
-- name    : BookProof.ChapterSirkRitzSpectrum.abs_re_inner_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:26:06.730333+00:00
-- url     : https://prove2.me/theorems/a1445d67-c797-497d-be6e-62211fa25cfc
-- title:
--   (T : F →L[ℂ] F) (x : F) : |(inner ℂ x (T x) : ℂ).re| ≤ ‖T‖ * ‖x‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.abs_re_inner_le` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.abs_re_inner_le
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.abs_re_inner_le (T : F →L[ℂ] F) (x : F) :
    |(inner ℂ x (T x) : ℂ).re| ≤ ‖T‖ * ‖x‖ ^ 2 := by sorry
