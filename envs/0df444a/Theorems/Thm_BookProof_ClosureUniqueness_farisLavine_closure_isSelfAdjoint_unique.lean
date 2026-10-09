-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_farisLavine_closure_isSelfAdjoint_unique
-- name    : BookProof.ClosureUniqueness.farisLavine_closure_isSelfAdjoint_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:47:28.225728+00:00
-- url     : https://prove2.me/theorems/e1a0d1b5-db7e-4882-9564-9f5f2340b35b
-- title:
--   `BookProof.ClosureUniqueness.farisLavine_closure_isSelfAdjoint_unique` (H N : D →ₗ[ℂ] F) (c : ℝ) (hdense : Dense (D : Set F)) (hH : SymmetricOn D H) (hN : SymmetricOn D N) (hc : 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.farisLavine_closure_isSelfAdjoint_unique` (H N : D →ₗ[ℂ] F) (c : ℝ) (hdense : Dense (D : Set F)) (hH : SymmetricOn D H) (hN : SymmetricOn D N) (hc : 0 ≤ c) (hNpos : ∀ x : D, 0 ≤ quadForm N x) (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f) (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) : IsClosureOf H (clExt H hdense hH) ∧ IsSelfAdjointExtension H (clExt H hdense hH) ∧ ∀ {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] F), IsSelfAdjointExtension H A → Dom = clDom H ∧ ∀ (x : F) (h : x ∈ Dom) (h' : x ∈ clDom H), A ⟨x, h⟩ = clExt H hdense hH ⟨x, h'⟩
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.farisLavine_closure_isSelfAdjoint_unique`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.farisLavine_closure_isSelfAdjoint_unique
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.ClosureUniqueness.farisLavine_closure_isSelfAdjoint_unique (H N : D →ₗ[ℂ] F) (c : ℝ)
    (hdense : Dense (D : Set F)) (hH : SymmetricOn D H) (hN : SymmetricOn D N) (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) :
    IsClosureOf H (clExt H hdense hH) ∧ IsSelfAdjointExtension H (clExt H hdense hH) ∧
      ∀ {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] F), IsSelfAdjointExtension H A →
        Dom = clDom H ∧ ∀ (x : F) (h : x ∈ Dom) (h' : x ∈ clDom H),
          A ⟨x, h⟩ = clExt H hdense hH ⟨x, h'⟩ := by sorry
