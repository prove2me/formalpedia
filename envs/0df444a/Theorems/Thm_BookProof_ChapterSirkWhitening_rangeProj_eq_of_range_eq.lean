-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_eq_of_range_eq
-- name    : BookProof.ChapterSirkWhitening.rangeProj_eq_of_range_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:47:39.699978+00:00
-- url     : https://prove2.me/theorems/d53a734a-a256-450b-8d3f-123e1748c27f
-- title:
--   (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E) (hV₁ : V₁.adjoint.comp V₁ = ContinuousLinearMap.id ℂ F) (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G) (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) (h21 : ∀ z :...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.rangeProj_eq_of_range_eq` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.rangeProj_eq_of_range_eq
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.rangeProj_eq_of_range_eq (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E)
    (hV₁ : V₁.adjoint.comp V₁ = ContinuousLinearMap.id ℂ F)
    (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G)
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z)
    (h21 : ∀ z : G, ∃ y : F, V₂ z = V₁ y) :
    rangeProj V₁ = rangeProj V₂ := by sorry
