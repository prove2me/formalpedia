-- Prove2me | Theorems.Thm_BookProof_ChapterSirkSpectralGeometry_sirk_end_to_end_shiftInvert
-- name    : BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvert
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:54:17.958445+00:00
-- url     : https://prove2.me/theorems/9bf84170-a0e1-44a6-b121-d9d3a9b6e22b
-- title:
--   {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F} (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) (V : G →L[ℂ] F) (qX qXinv...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvert` (module `BookProof.ChapterSirkSpectralGeometry`), source chapter `BookProof/ChapterChapterSirkSpectralGeometry.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkSpectralGeometry.lean

-- Generated from ChapterSirkSpectralGeometry.lean — theorem BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvert
import Mathlib
import Definitions.Def_ChapterSirkSpectralGeometry
open BookProof.ChapterSirkSpectralGeometry








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.HashimotoShiftInvert BookProof.FarisLavine






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}







variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvert
    {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (hR : IsShiftInvert A γ R) (hsym : SymmetricOn Dom A)
    (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ)
    (V : G →L[ℂ] F) (qX qXinv : F →L[ℂ] F) (qBinv : G →L[ℂ] G) (p : Polynomial ℂ)
    (flow psiX : F →L[ℂ] F) (psiB : G →L[ℂ] G) (C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ G)
    (hViso : ∀ x : G, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : F, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : G, ∃ y : G, R (V x) = V y)
    (hinvq : ∀ x : G, ∃ y : G, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ F)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ G)
    (hflow : flow = psiX)
    (hcxX : numRange R ⊆ realSegment 0 γ⁻¹ →
      ‖psiX - (Polynomial.aeval R p).comp qXinv‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcxB : numRange (compress V R) ⊆ realSegment 0 γ⁻¹ →
      ‖psiB - (Polynomial.aeval (compress V R) p).comp qBinv‖
        ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : F) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by sorry
