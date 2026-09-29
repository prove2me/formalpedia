-- Prove2me | Theorems.Thm_BookProof_ChapterSirkSpectralGeometry_crouzeix_domain_shiftInvert
-- name    : BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvert
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:54:03.217977+00:00
-- url     : https://prove2.me/theorems/1d19a775-0591-4639-ad4c-58953e55f56e
-- title:
--   {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F} (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A) (hpos...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvert` (module `BookProof.ChapterSirkSpectralGeometry`), source chapter `BookProof/ChapterChapterSirkSpectralGeometry.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkSpectralGeometry.lean

-- Generated from ChapterSirkSpectralGeometry.lean — theorem BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvert
import Mathlib
import Definitions.Def_ChapterSirkSpectralGeometry
open BookProof.ChapterSirkSpectralGeometry








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}

theorem BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvert {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ)
    (V : G →L[ℂ] F) (hViso : ∀ x : G, ‖V x‖ = ‖x‖) :
    convexHull ℝ (numRange (compress V R)) ⊆ realSegment 0 γ⁻¹ := by sorry
