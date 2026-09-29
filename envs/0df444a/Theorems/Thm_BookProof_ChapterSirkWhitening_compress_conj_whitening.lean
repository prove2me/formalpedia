-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_compress_conj_whitening
-- name    : BookProof.ChapterSirkWhitening.compress_conj_whitening
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:47:02.69288+00:00
-- url     : https://prove2.me/theorems/676c43c2-db0d-4b3e-8d7d-bf5a52051b86
-- title:
--   (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E) (X : E →L[ℂ] E) (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G) (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) : compress V₁ X = (whiteningEquiv V₂ V₁).comp ((compr...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.compress_conj_whitening` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.compress_conj_whitening
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.compress_conj_whitening (V₁ : F →L[ℂ] E) (V₂ : G →L[ℂ] E) (X : E →L[ℂ] E)
    (hV₂ : V₂.adjoint.comp V₂ = ContinuousLinearMap.id ℂ G)
    (h12 : ∀ y : F, ∃ z : G, V₁ y = V₂ z) :
    compress V₁ X
      = (whiteningEquiv V₂ V₁).comp ((compress V₂ X).comp (whiteningEquiv V₁ V₂)) := by sorry
