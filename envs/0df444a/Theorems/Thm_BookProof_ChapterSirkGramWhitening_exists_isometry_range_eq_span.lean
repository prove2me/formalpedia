-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_exists_isometry_range_eq_span
-- name    : BookProof.ChapterSirkGramWhitening.exists_isometry_range_eq_span
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T08:01:33.176506+00:00
-- url     : https://prove2.me/theorems/647ad2fa-415b-43a0-809d-452b7f675d5a
-- title:
--   {m : ℕ} (w : Fin m → E) : ∃ (d : ℕ) (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E), d = Module.finrank ℂ (Submodule.span ℂ (Set.range w)) ∧ (ContinuousLinearMap.adjoint V).comp V =...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.exists_isometry_range_eq_span` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.exists_isometry_range_eq_span
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.exists_isometry_range_eq_span {m : ℕ} (w : Fin m → E) :
    ∃ (d : ℕ) (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E),
      d = Module.finrank ℂ (Submodule.span ℂ (Set.range w)) ∧
      (ContinuousLinearMap.adjoint V).comp V = ContinuousLinearMap.id ℂ
        (EuclideanSpace ℂ (Fin d)) ∧
      LinearMap.range (V : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E)
        = Submodule.span ℂ (Set.range w) := by sorry
