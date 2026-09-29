-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_le_rayleigh_iff_le_spectrum
-- name    : BookProof.ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:42:27.295642+00:00
-- url     : https://prove2.me/theorems/3f43e518-b9ff-42e4-9e81-5d54fe2d60a3
-- title:
--   (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (c : ℝ) : (∀ x : F, c * ‖x‖ ^ 2 ≤ (inner ℂ x (T x) : ℂ).re) ↔ ∀ μ ∈ spectrum ℝ T, c ≤ μ
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum` (module `BookProof.ChapterSirkRitzSpectrum`), source chapter `BookProof/ChapterChapterSirkRitzSpectrum.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRitzSpectrum.lean

-- Generated from ChapterSirkRitzSpectrum.lean — theorem BookProof.ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
open BookProof.ChapterSirkRitzSpectrum







noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (c : ℝ) :
    (∀ x : F, c * ‖x‖ ^ 2 ≤ (inner ℂ x (T x) : ℂ).re) ↔ ∀ μ ∈ spectrum ℝ T, c ≤ μ := by sorry
