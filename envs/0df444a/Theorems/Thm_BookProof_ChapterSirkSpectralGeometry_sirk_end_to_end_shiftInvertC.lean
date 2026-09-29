-- Prove2me | Theorems.Thm_BookProof_ChapterSirkSpectralGeometry_sirk_end_to_end_shiftInvertC
-- name    : BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvertC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:54:25.468275+00:00
-- url     : https://prove2.me/theorems/c315f663-29ff-46b4-83f2-52e7f740735f
-- title:
--   {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F} (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) (V : G →L[ℂ] F) (qX qXinv : F →L[ℂ] F) (qBinv : G...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvertC` (module `BookProof.ChapterSirkSpectralGeometry`), source chapter `BookProof/ChapterChapterSirkSpectralGeometry.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkSpectralGeometry.lean

-- Generated from ChapterSirkSpectralGeometry.lean — theorem BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvertC
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

theorem BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_shiftInvertC
    {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0)
    (V : G →L[ℂ] F) (qX qXinv : F →L[ℂ] F) (qBinv : G →L[ℂ] G) (p : Polynomial ℂ)
    (flow psiX : F →L[ℂ] F) (psiB : G →L[ℂ] G) (C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ G)
    (hViso : ∀ x : G, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : F, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : G, ∃ y : G, X (V x) = V y)
    (hinvq : ∀ x : G, ∃ y : G, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ F)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ G)
    (hflow : flow = psiX)
    (hcxX : numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ →
      ‖psiX - (Polynomial.aeval X p).comp qXinv‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcxB : numRange (compress V X) ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ →
      ‖psiB - (Polynomial.aeval (compress V X) p).comp qBinv‖
        ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : F) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by sorry
