-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_factorGraph_eq_of_isCoreOf_pair
-- name    : BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf_pair
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:45:31.985027+00:00
-- url     : https://prove2.me/theorems/051a0e64-6e6a-4773-9e45-79579becbf1e
-- title:
--   `BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf_pair` {T : D →ₗ[ℂ] F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h₁ : IsCoreOf T₁ T) (h₂ : IsCoreOf T₂ T) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf_pair` {T : D →ₗ[ℂ] F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h₁ : IsCoreOf T₁ T) (h₂ : IsCoreOf T₂ T) : factorGraph T₁ = factorGraph T₂
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf_pair`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf_pair
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf_pair {T : D →ₗ[ℂ] F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F}
    (h₁ : IsCoreOf T₁ T) (h₂ : IsCoreOf T₂ T) : factorGraph T₁ = factorGraph T₂ := by sorry
