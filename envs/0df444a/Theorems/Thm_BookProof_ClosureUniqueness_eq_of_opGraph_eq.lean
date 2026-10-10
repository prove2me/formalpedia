-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_eq_of_opGraph_eq
-- name    : BookProof.ClosureUniqueness.eq_of_opGraph_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:41:51.824037+00:00
-- url     : https://prove2.me/theorems/09012883-0fab-4528-9609-a9c0c8cfee47
-- title:
--   `BookProof.ClosureUniqueness.eq_of_opGraph_eq` {A : Dom₁ →ₗ[ℂ] F} {B : Dom₂ →ₗ[ℂ] F} (h : opGraph A = opGraph B) : Dom₁ = Dom₂ ∧ ∀ (x : F) (h₁ : x ∈ Dom₁) (h₂ :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.eq_of_opGraph_eq` {A : Dom₁ →ₗ[ℂ] F} {B : Dom₂ →ₗ[ℂ] F} (h : opGraph A = opGraph B) : Dom₁ = Dom₂ ∧ ∀ (x : F) (h₁ : x ∈ Dom₁) (h₂ : x ∈ Dom₂), A ⟨x, h₁⟩ = B ⟨x, h₂⟩
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.eq_of_opGraph_eq`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.eq_of_opGraph_eq
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.eq_of_opGraph_eq {A : Dom₁ →ₗ[ℂ] F} {B : Dom₂ →ₗ[ℂ] F} (h : opGraph A = opGraph B) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (h₁ : x ∈ Dom₁) (h₂ : x ∈ Dom₂), A ⟨x, h₁⟩ = B ⟨x, h₂⟩ := by sorry
