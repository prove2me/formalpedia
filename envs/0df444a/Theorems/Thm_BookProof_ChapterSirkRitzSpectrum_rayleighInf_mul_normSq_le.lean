-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_rayleighInf_mul_normSq_le
-- name    : BookProof.ChapterSirkRitzSpectrum.rayleighInf_mul_normSq_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:46:59.695638+00:00
-- url     : https://prove2.me/theorems/284512a9-eba9-45e1-b7e7-7a64d352682a
-- title:
--   [Nontrivial F] (T : F →L[ℂ] F) (x : F) : rayleighInf T * ‖x‖ ^ 2 ≤ (inner ℂ x (T x) : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.rayleighInf_mul_normSq_le` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.rayleighInf_mul_normSq_le
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.rayleighInf_mul_normSq_le [Nontrivial F] (T : F →L[ℂ] F) (x : F) :
    rayleighInf T * ‖x‖ ^ 2 ≤ (inner ℂ x (T x) : ℂ).re := by sorry
