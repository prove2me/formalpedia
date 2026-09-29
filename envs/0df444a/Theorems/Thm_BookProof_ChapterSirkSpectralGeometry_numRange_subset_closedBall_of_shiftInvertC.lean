-- Prove2me | Theorems.Thm_BookProof_ChapterSirkSpectralGeometry_numRange_subset_closedBall_of_shiftInvertC
-- name    : BookProof.ChapterSirkSpectralGeometry.numRange_subset_closedBall_of_shiftInvertC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:32:52.559444+00:00
-- url     : https://prove2.me/theorems/b99be305-97de-458f-bb51-8010feb51f18
-- title:
--   {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F} (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) : numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkSpectralGeometry.numRange_subset_closedBall_of_shiftInvertC` (module `BookProof.ChapterSirkSpectralGeometry`), source chapter `BookProof/ChapterChapterSirkSpectralGeometry.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkSpectralGeometry.lean

-- Generated from ChapterSirkSpectralGeometry.lean — theorem BookProof.ChapterSirkSpectralGeometry.numRange_subset_closedBall_of_shiftInvertC
import Mathlib
import Definitions.Def_ChapterSirkSpectralGeometry
open BookProof.ChapterSirkSpectralGeometry








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}

theorem BookProof.ChapterSirkSpectralGeometry.numRange_subset_closedBall_of_shiftInvertC {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) :
    numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ := by sorry
