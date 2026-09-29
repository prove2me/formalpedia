-- Prove2me | Theorems.Thm_BookProof_ChapterH9_exists_unit_eigenvector
-- name    : BookProof.ChapterH9.exists_unit_eigenvector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:35:29.290984+00:00
-- url     : https://prove2.me/theorems/f223f616-c290-44e1-a45c-257c6b5b0fa8
-- title:
--   The Lean 4 theorem `exists_unit_eigenvector` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `exists_unit_eigenvector` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.exists_unit_eigenvector
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9


noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace E] [CompleteSpace F] in

theorem BookProof.ChapterH9.exists_unit_eigenvector [FiniteDimensional ℂ F] (A : F →L[ℂ] F) {lam : ℂ}
    (hlam : lam ∈ spectrum ℂ (A : F →ₗ[ℂ] F)) : ∃ y : F, ‖y‖ = 1 ∧ A y = lam • y := by sorry
