-- Prove2me | Theorems.Thm_BookProof_ChapterSirkSpectralGeometry_numRange_subset_realSegment_of_shiftInvert
-- name    : BookProof.ChapterSirkSpectralGeometry.numRange_subset_realSegment_of_shiftInvert
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:33:32.554647+00:00
-- url     : https://prove2.me/theorems/7b0633e9-1faa-4ac6-bae1-433e9fd09ce3
-- title:
--   {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F} (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) : numRange R ⊆ realSegment 0 γ⁻¹
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkSpectralGeometry.numRange_subset_realSegment_of_shiftInvert` (module `BookProof.ChapterSirkSpectralGeometry`), source chapter `BookProof/ChapterChapterSirkSpectralGeometry.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkSpectralGeometry.lean

-- Generated from ChapterSirkSpectralGeometry.lean — theorem BookProof.ChapterSirkSpectralGeometry.numRange_subset_realSegment_of_shiftInvert
import Mathlib
import Definitions.Def_ChapterSirkSpectralGeometry
open BookProof.ChapterSirkSpectralGeometry








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}

theorem BookProof.ChapterSirkSpectralGeometry.numRange_subset_realSegment_of_shiftInvert {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) :
    numRange R ⊆ realSegment 0 γ⁻¹ := by sorry
