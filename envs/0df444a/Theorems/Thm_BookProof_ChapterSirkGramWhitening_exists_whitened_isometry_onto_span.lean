-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_exists_whitened_isometry_onto_span
-- name    : BookProof.ChapterSirkGramWhitening.exists_whitened_isometry_onto_span
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:56.667131+00:00
-- url     : https://prove2.me/theorems/04686db0-d0b1-46e7-9e6d-ce4a53969cbb
-- title:
--   {m : ℕ} {w : Fin m → E} (hw : LinearIndependent ℂ w) : ∃ T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m), IsWhitening w T ∧ (ContinuousLinearMap.adjoint (whitened w...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.exists_whitened_isometry_onto_span` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.exists_whitened_isometry_onto_span
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.exists_whitened_isometry_onto_span {m : ℕ} {w : Fin m → E}
    (hw : LinearIndependent ℂ w) :
    ∃ T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m),
      IsWhitening w T ∧
      (ContinuousLinearMap.adjoint (whitened w T)).comp (whitened w T)
        = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) ∧
      LinearMap.range (whitened w T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
        = Submodule.span ℂ (Set.range w) := by sorry
