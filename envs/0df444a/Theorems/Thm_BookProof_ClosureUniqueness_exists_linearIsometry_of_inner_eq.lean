-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_exists_linearIsometry_of_inner_eq
-- name    : BookProof.ClosureUniqueness.exists_linearIsometry_of_inner_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:43:29.231906+00:00
-- url     : https://prove2.me/theorems/d3bd1f28-8802-4f05-970b-0d16b98c975c
-- title:
--   `BookProof.ClosureUniqueness.exists_linearIsometry_of_inner_eq` (B C : D →ₗ[ℂ] F) (h : ∀ x y : D, (inner ℂ (B x) (B y) : ℂ) = inner ℂ (C x) (C y)) : ∃ U : LinearMap.range B...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.exists_linearIsometry_of_inner_eq` (B C : D →ₗ[ℂ] F) (h : ∀ x y : D, (inner ℂ (B x) (B y) : ℂ) = inner ℂ (C x) (C y)) : ∃ U : LinearMap.range B →ₗ[ℂ] F, (∀ x : D, U ⟨B x, LinearMap.mem_range_self B x⟩ = C x) ∧ (∀ z : LinearMap.range B, ‖U z‖ = ‖(z : F)‖) ∧ LinearMap.range U = LinearMap.range C
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.exists_linearIsometry_of_inner_eq`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.exists_linearIsometry_of_inner_eq
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.exists_linearIsometry_of_inner_eq (B C : D →ₗ[ℂ] F)
    (h : ∀ x y : D, (inner ℂ (B x) (B y) : ℂ) = inner ℂ (C x) (C y)) :
    ∃ U : LinearMap.range B →ₗ[ℂ] F,
      (∀ x : D, U ⟨B x, LinearMap.mem_range_self B x⟩ = C x) ∧
      (∀ z : LinearMap.range B, ‖U z‖ = ‖(z : F)‖) ∧
      LinearMap.range U = LinearMap.range C := by sorry
