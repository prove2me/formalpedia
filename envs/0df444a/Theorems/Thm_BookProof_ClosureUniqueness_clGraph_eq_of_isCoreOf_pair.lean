-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_clGraph_eq_of_isCoreOf_pair
-- name    : BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf_pair
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:44:43.894272+00:00
-- url     : https://prove2.me/theorems/fa9c3d32-c047-454f-849e-976f0ff3b801
-- title:
--   `BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf_pair` {T : D →ₗ[ℂ] F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h₁ : IsCoreOf T₁ T) (h₂ : IsCoreOf T₂ T) : clGraph...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf_pair` {T : D →ₗ[ℂ] F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h₁ : IsCoreOf T₁ T) (h₂ : IsCoreOf T₂ T) : clGraph T₁ = clGraph T₂
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf_pair`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf_pair
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf_pair {T : D →ₗ[ℂ] F} {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F}
    (h₁ : IsCoreOf T₁ T) (h₂ : IsCoreOf T₂ T) : clGraph T₁ = clGraph T₂ := by sorry
