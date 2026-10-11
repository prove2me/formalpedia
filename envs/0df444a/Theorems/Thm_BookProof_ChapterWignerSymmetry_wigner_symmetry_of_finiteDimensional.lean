-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_wigner_symmetry_of_finiteDimensional
-- name    : BookProof.ChapterWignerSymmetry.wigner_symmetry_of_finiteDimensional
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:19:19.867182+00:00
-- url     : https://prove2.me/theorems/89503ee9-7381-4c42-9a2c-03c590d2ac70
-- title:
--   `BookProof.ChapterWignerSymmetry.wigner_symmetry_of_finiteDimensional` {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [Nontrivial F] {T : F → F}
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.wigner_symmetry_of_finiteDimensional` {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [Nontrivial F] {T : F → F} (hT : IsWignerSymmetry T) : (∃ U : F ≃ₗᵢ[ℂ] F, ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) ∨ (∃ U : F → F, IsAntiunitary U ∧ ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.wigner_symmetry_of_finiteDimensional`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.wigner_symmetry_of_finiteDimensional
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}
variable {b : OrthonormalBasis ι ℂ E} {o : ι}

theorem BookProof.ChapterWignerSymmetry.wigner_symmetry_of_finiteDimensional {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [Nontrivial F] {T : F → F}
    (hT : IsWignerSymmetry T) :
    (∃ U : F ≃ₗᵢ[ℂ] F, ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) ∨
    (∃ U : F → F, IsAntiunitary U ∧ ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) := by sorry
