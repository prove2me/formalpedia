-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_re_inner_comm
-- name    : BookProof.ChapterSirkRitzSpectrum.re_inner_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:27:22.161266+00:00
-- url     : https://prove2.me/theorems/b1e59ecb-396a-43e3-b337-cccf7b10df0d
-- title:
--   (T : F →L[ℂ] F) (x : F) : (inner ℂ (T x) x : ℂ).re = (inner ℂ x (T x) : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.re_inner_comm` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.re_inner_comm
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.re_inner_comm (T : F →L[ℂ] F) (x : F) :
    (inner ℂ (T x) x : ℂ).re = (inner ℂ x (T x) : ℂ).re := by sorry
