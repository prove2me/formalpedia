-- Prove2me | Theorems.Thm_BookProof_ChapterSirkSpectralGeometry_crouzeix_domain_shiftInvertC
-- name    : BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvertC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:54:13.819741+00:00
-- url     : https://prove2.me/theorems/9ef4571a-8368-4990-a531-a12a2921f33f
-- title:
--   {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F} (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvertC` (module `BookProof.ChapterSirkSpectralGeometry`), source chapter `BookProof/ChapterChapterSirkSpectralGeometry.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkSpectralGeometry.lean

-- Generated from ChapterSirkSpectralGeometry.lean — theorem BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvertC
import Mathlib
import Definitions.Def_ChapterSirkSpectralGeometry
open BookProof.ChapterSirkSpectralGeometry








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}

theorem BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvertC {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0)
    (V : G →L[ℂ] F) (hViso : ∀ x : G, ‖V x‖ = ‖x‖) :
    convexHull ℝ (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ := by sorry
