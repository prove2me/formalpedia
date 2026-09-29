-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_adjoint_comp_rangeProj
-- name    : BookProof.ChapterSirkWhitening.adjoint_comp_rangeProj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:12:30.400522+00:00
-- url     : https://prove2.me/theorems/6fa3e7ef-cee2-475a-ab5f-47a898b68d6e
-- title:
--   (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E) (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G) (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) : V₁.adjoint.comp (rangeProj V₂) = V₁.adjoint
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.adjoint_comp_rangeProj` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.adjoint_comp_rangeProj
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.adjoint_comp_rangeProj (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E)
    (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G)
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) :
    V₁.adjoint.comp (rangeProj V₂) = V₁.adjoint := by sorry
