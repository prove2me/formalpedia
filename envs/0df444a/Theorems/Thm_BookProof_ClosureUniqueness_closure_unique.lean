-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_closure_unique
-- name    : BookProof.ClosureUniqueness.closure_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:44:34.783095+00:00
-- url     : https://prove2.me/theorems/914f4df1-55fa-4fed-b387-13800309215e
-- title:
--   `BookProof.ClosureUniqueness.closure_unique` {T : D →ₗ[ℂ] F} {A : Dom₁ →ₗ[ℂ] F} {B : Dom₂ →ₗ[ℂ] F} (hA : IsClosureOf T A) (hB : IsClosureOf T B) : Dom₁ = Dom₂ ∧ ∀ (x...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.closure_unique` {T : D →ₗ[ℂ] F} {A : Dom₁ →ₗ[ℂ] F} {B : Dom₂ →ₗ[ℂ] F} (hA : IsClosureOf T A) (hB : IsClosureOf T B) : Dom₁ = Dom₂ ∧ ∀ (x : F) (h₁ : x ∈ Dom₁) (h₂ : x ∈ Dom₂), A ⟨x, h₁⟩ = B ⟨x, h₂⟩
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.closure_unique`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.closure_unique
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.closure_unique {T : D →ₗ[ℂ] F} {A : Dom₁ →ₗ[ℂ] F} {B : Dom₂ →ₗ[ℂ] F}
    (hA : IsClosureOf T A) (hB : IsClosureOf T B) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (h₁ : x ∈ Dom₁) (h₂ : x ∈ Dom₂), A ⟨x, h₁⟩ = B ⟨x, h₂⟩ := by sorry
