-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_re_inner_real_smul
-- name    : BookProof.ChapterSirkRitzSpectrum.re_inner_real_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:28:06.071647+00:00
-- url     : https://prove2.me/theorems/8a190517-eb1b-46a0-b1a7-ec58a1bbc262
-- title:
--   (T : F →L[ℂ] F) (c : ℝ) (x : F) : (inner ℂ ((c : ℂ) • x) (T ((c : ℂ) • x)) : ℂ).re = c ^ 2 * (inner ℂ x (T x) : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.re_inner_real_smul` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.re_inner_real_smul
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.re_inner_real_smul (T : F →L[ℂ] F) (c : ℝ) (x : F) :
    (inner ℂ ((c : ℂ) • x) (T ((c : ℂ) • x)) : ℂ).re = c ^ 2 * (inner ℂ x (T x) : ℂ).re := by sorry
