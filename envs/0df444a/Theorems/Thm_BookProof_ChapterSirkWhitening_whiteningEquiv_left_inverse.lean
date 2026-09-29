-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_whiteningEquiv_left_inverse
-- name    : BookProof.ChapterSirkWhitening.whiteningEquiv_left_inverse
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:42:07.624384+00:00
-- url     : https://prove2.me/theorems/c5f4d72a-f398-43c2-97fd-d6780a12ab69
-- title:
--   (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E) (hV₁ : V₁.adjoint.comp V₁ = ContinuousLinearMap.id ℂ F) (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G) (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) (y : F) : whi...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.whiteningEquiv_left_inverse` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.whiteningEquiv_left_inverse
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.whiteningEquiv_left_inverse (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E)
    (hV₁ : V₁.adjoint.comp V₁ = ContinuousLinearMap.id ℂ F)
    (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G)
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) (y : F) :
    whiteningEquiv V₂ V₁ (whiteningEquiv V₁ V₂ y) = y := by sorry
