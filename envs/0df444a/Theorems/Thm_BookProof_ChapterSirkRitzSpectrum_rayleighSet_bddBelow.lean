-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_rayleighSet_bddBelow
-- name    : BookProof.ChapterSirkRitzSpectrum.rayleighSet_bddBelow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:44:43.407198+00:00
-- url     : https://prove2.me/theorems/88169861-fca0-4ac7-9fcb-1598e8f5ed43
-- title:
--   (T : F →L[ℂ] F) : BddBelow (rayleighSet T)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.rayleighSet_bddBelow` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.rayleighSet_bddBelow
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.rayleighSet_bddBelow (T : F →L[ℂ] F) : BddBelow (rayleighSet T) := by sorry
