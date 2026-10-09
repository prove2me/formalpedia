-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_factorGraph_eq_of_isCoreOf
-- name    : BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:43:08.09816+00:00
-- url     : https://prove2.me/theorems/97259a89-4f46-49d7-be3a-8298b9f7ee62
-- title:
--   `BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf` {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : IsCoreOf T₁ T₂) : factorGraph T₁ = factorGraph T₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf` {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : IsCoreOf T₁ T₂) : factorGraph T₁ = factorGraph T₂
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : IsCoreOf T₁ T₂) :
    factorGraph T₁ = factorGraph T₂ := by sorry
