-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_farisLavine_clGraph_eq_of_cores
-- name    : BookProof.ClosureUniqueness.farisLavine_clGraph_eq_of_cores
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:45:27.773099+00:00
-- url     : https://prove2.me/theorems/20f7e46c-9f5a-49a1-aba1-34dd5e53a1a4
-- title:
--   `BookProof.ClosureUniqueness.farisLavine_clGraph_eq_of_cores` {T : D →ₗ[ℂ] F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h₁ : IsCoreOf T₁ T) (h₂ : IsCoreOf T₂ T) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.farisLavine_clGraph_eq_of_cores` {T : D →ₗ[ℂ] F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h₁ : IsCoreOf T₁ T) (h₂ : IsCoreOf T₂ T) : clGraph T₁ = clGraph T₂ ∧ clDom T₁ = clDom T₂ ∧ adjGraph T₁ = adjGraph T₂
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.farisLavine_clGraph_eq_of_cores`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.farisLavine_clGraph_eq_of_cores
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.ClosureUniqueness.farisLavine_clGraph_eq_of_cores {T : D →ₗ[ℂ] F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F}
    (h₁ : IsCoreOf T₁ T) (h₂ : IsCoreOf T₂ T) :
    clGraph T₁ = clGraph T₂ ∧ clDom T₁ = clDom T₂ ∧ adjGraph T₁ = adjGraph T₂ := by sorry
