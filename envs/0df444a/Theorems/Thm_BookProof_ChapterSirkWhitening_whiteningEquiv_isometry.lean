-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_whiteningEquiv_isometry
-- name    : BookProof.ChapterSirkWhitening.whiteningEquiv_isometry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:41:31.772276+00:00
-- url     : https://prove2.me/theorems/c5f6d3ee-2c19-42ed-b315-c46a92e5fff3
-- title:
--   (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E) (hV₁ : ∀ y : F, ‖V₁ y‖ = ‖y‖) (hV₂ : ∀ z : G, ‖V₂ z‖ = ‖z‖) (hV₂adj : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G) (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) (y : F...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.whiteningEquiv_isometry` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.whiteningEquiv_isometry
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.whiteningEquiv_isometry (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E)
    (hV₁ : ∀ y : F, ‖V₁ y‖ = ‖y‖) (hV₂ : ∀ z : G, ‖V₂ z‖ = ‖z‖)
    (hV₂adj : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G)
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) (y : F) :
    ‖whiteningEquiv V₁ V₂ y‖ = ‖y‖ := by sorry
