-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_comp_of_le
-- name    : BookProof.ChapterSirkWhitening.rangeProj_comp_of_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:13:02.554088+00:00
-- url     : https://prove2.me/theorems/12e6c9bd-6344-4783-b5f2-3739e03c7838
-- title:
--   (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E) (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G) (hle : ∀ y : F, ∃ z : G, V₁ y = V₂ z) : (rangeProj V₂).comp (rangeProj V₁) = rangeProj V₁
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.rangeProj_comp_of_le` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.rangeProj_comp_of_le
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.rangeProj_comp_of_le (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E)
    (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G)
    (hle : ∀ y : F, ∃ z : G, V₁ y = V₂ z) :
    (rangeProj V₂).comp (rangeProj V₁) = rangeProj V₁ := by sorry
