-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_exists_isometry_fin_range_eq_span
-- name    : BookProof.ChapterSirkGramWhitening.exists_isometry_fin_range_eq_span
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T08:01:03.018167+00:00
-- url     : https://prove2.me/theorems/2620638d-3e9c-444f-aa19-10e2056657ca
-- title:
--   {m : ℕ} {w : Fin m → E} (hw : LinearIndependent ℂ w) : ∃ V : EuclideanSpace ℂ (Fin m) →L[ℂ] E, (ContinuousLinearMap.adjoint V).comp V = ContinuousLinearMap.id ℂ (EuclideanSpace...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.exists_isometry_fin_range_eq_span` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.exists_isometry_fin_range_eq_span
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.exists_isometry_fin_range_eq_span {m : ℕ} {w : Fin m → E}
    (hw : LinearIndependent ℂ w) :
    ∃ V : EuclideanSpace ℂ (Fin m) →L[ℂ] E,
      (ContinuousLinearMap.adjoint V).comp V = ContinuousLinearMap.id ℂ
        (EuclideanSpace ℂ (Fin m)) ∧
      LinearMap.range (V : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
        = Submodule.span ℂ (Set.range w) := by sorry
