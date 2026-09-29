-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_re_inner_sub_algebraMap
-- name    : BookProof.ChapterSirkRitzSpectrum.re_inner_sub_algebraMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:28:44.556676+00:00
-- url     : https://prove2.me/theorems/d5631509-63aa-42ac-b7e5-5572ca8f07d0
-- title:
--   (T : F →L[ℂ] F) (c : ℝ) (x : F) : (inner ℂ ((T - (algebraMap ℝ (F →L[ℂ] F)) c) x) x : ℂ).re = (inner ℂ (T x) x : ℂ).re - c * ‖x‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.re_inner_sub_algebraMap` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.re_inner_sub_algebraMap
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.re_inner_sub_algebraMap (T : F →L[ℂ] F) (c : ℝ) (x : F) :
    (inner ℂ ((T - (algebraMap ℝ (F →L[ℂ] F)) c) x) x : ℂ).re
      = (inner ℂ (T x) x : ℂ).re - c * ‖x‖ ^ 2 := by sorry
