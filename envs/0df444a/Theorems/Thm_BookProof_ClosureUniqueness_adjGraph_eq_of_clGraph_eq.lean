-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_adjGraph_eq_of_clGraph_eq
-- name    : BookProof.ClosureUniqueness.adjGraph_eq_of_clGraph_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:42:37.18223+00:00
-- url     : https://prove2.me/theorems/f3a7b127-f29d-41f7-95ea-71d531a6461e
-- title:
--   `BookProof.ClosureUniqueness.adjGraph_eq_of_clGraph_eq` {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : clGraph T₁ = clGraph T₂) : adjGraph T₁ = adjGraph T₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.adjGraph_eq_of_clGraph_eq` {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F} (h : clGraph T₁ = clGraph T₂) : adjGraph T₁ = adjGraph T₂
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.adjGraph_eq_of_clGraph_eq`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.adjGraph_eq_of_clGraph_eq
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.adjGraph_eq_of_clGraph_eq {T₁ : D₁ →ₗ[ℂ] F} {T₂ : D₂ →ₗ[ℂ] F}
    (h : clGraph T₁ = clGraph T₂) : adjGraph T₁ = adjGraph T₂ := by sorry
