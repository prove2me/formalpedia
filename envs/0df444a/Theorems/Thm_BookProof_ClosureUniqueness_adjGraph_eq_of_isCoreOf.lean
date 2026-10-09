-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_adjGraph_eq_of_isCoreOf
-- name    : BookProof.ClosureUniqueness.adjGraph_eq_of_isCoreOf
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:43:05.052991+00:00
-- url     : https://prove2.me/theorems/cd4a0b0e-24d1-4911-b63b-13c0b6b95084
-- title:
--   `BookProof.ClosureUniqueness.adjGraph_eq_of_isCoreOf` {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : IsCoreOf T₁ T₂) : adjGraph T₁ = adjGraph T₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.adjGraph_eq_of_isCoreOf` {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : IsCoreOf T₁ T₂) : adjGraph T₁ = adjGraph T₂
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.adjGraph_eq_of_isCoreOf`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.adjGraph_eq_of_isCoreOf
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.adjGraph_eq_of_isCoreOf {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : IsCoreOf T₁ T₂) :
    adjGraph T₁ = adjGraph T₂ := by sorry
