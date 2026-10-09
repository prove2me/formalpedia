-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_clGraph_eq_of_isCoreOf
-- name    : BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:42:07.904839+00:00
-- url     : https://prove2.me/theorems/f9986bb2-3a7a-487f-a676-869cd3a93f6f
-- title:
--   `BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf` {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : IsCoreOf T₁ T₂) : clGraph T₁ = clGraph T₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf` {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : IsCoreOf T₁ T₂) : clGraph T₁ = clGraph T₂
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : IsCoreOf T₁ T₂) :
    clGraph T₁ = clGraph T₂ := by sorry
