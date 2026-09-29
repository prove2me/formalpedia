-- Prove2me | Theorems.Thm_BookProof_ChapterSirkSpectralGeometry_sirk_end_to_end_crouzeix_domain
-- name    : BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_crouzeix_domain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:50:03.609116+00:00
-- url     : https://prove2.me/theorems/5a221ee8-e77b-4f6c-bc22-6e66cac91250
-- title:
--   (V : G →L[ℂ] E) (X qX qXinv : E →L[ℂ] E) (qBinv : G →L[ℂ] G) (p : Polynomial ℂ) (flow psiX : E →L[ℂ] E) (psiB : G →L[ℂ] G) (C Dmin h : ℝ) (m : ℕ) (S : Set ℂ) (hS : numRange X ⊆ S) (hVV :...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_crouzeix_domain` (module `BookProof.ChapterSirkSpectralGeometry`), source chapter `BookProof/ChapterChapterSirkSpectralGeometry.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkSpectralGeometry.lean

-- Generated from ChapterSirkSpectralGeometry.lean — theorem BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_crouzeix_domain
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

theorem BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_crouzeix_domain
    (V : G →L[ℂ] E) (X qX qXinv : E →L[ℂ] E) (qBinv : G →L[ℂ] G) (p : Polynomial ℂ)
    (flow psiX : E →L[ℂ] E) (psiB : G →L[ℂ] G)
    (C Dmin h : ℝ) (m : ℕ) (S : Set ℂ)
    (hS : numRange X ⊆ S)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ G)
    (hViso : ∀ x : G, ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : G, ∃ y : G, X (V x) = V y)
    (hinvq : ∀ x : G, ∃ y : G, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ G)
    (hflow : flow = psiX)
    (hcxX : numRange X ⊆ S →
      ‖psiX - (Polynomial.aeval X p).comp qXinv‖ ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcxB : numRange (compress V X) ⊆ S →
      ‖psiB - (Polynomial.aeval (compress V X) p).comp qBinv‖
        ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hv : V (V.adjoint v) = v) :
    ‖flow v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by sorry
