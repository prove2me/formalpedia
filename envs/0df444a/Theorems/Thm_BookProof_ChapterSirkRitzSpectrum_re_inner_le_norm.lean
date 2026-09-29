-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_re_inner_le_norm
-- name    : BookProof.ChapterSirkRitzSpectrum.re_inner_le_norm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:41:46.92011+00:00
-- url     : https://prove2.me/theorems/b19e1247-b869-438d-89c6-3a930371749b
-- title:
--   (T : F →L[ℂ] F) (x : F) : (inner ℂ x (T x) : ℂ).re ≤ ‖T‖ * ‖x‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.re_inner_le_norm` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.re_inner_le_norm
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.re_inner_le_norm (T : F →L[ℂ] F) (x : F) :
    (inner ℂ x (T x) : ℂ).re ≤ ‖T‖ * ‖x‖ ^ 2 := by sorry
