-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_friedrichsSqExtension_unique
-- name    : BookProof.FriedrichsSquare.friedrichsSqExtension_unique
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T00:41:17.723509+00:00
-- url     : https://prove2.me/theorems/8834791f-4386-4b61-b6dd-9266a8558147
-- title:
--   `BookProof.FriedrichsSquare.friedrichsSqExtension_unique` [CompleteSpace F] {A : D →ₗ[ℂ] F} (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D} {R₁ R₂ : Submodule ℂ (F × F)}
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.friedrichsSqExtension_unique` [CompleteSpace F] {A : D →ₗ[ℂ] F} (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D} {R₁ R₂ : Submodule ℂ (F × F)} (h₁ : IsFriedrichsSqExtension A hstab R₁) (h₂ : IsFriedrichsSqExtension A hstab R₂) : R₁ = R₂
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.friedrichsSqExtension_unique`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.friedrichsSqExtension_unique
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterClosureUniqueness
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.FriedrichsSquare.friedrichsSqExtension_unique [CompleteSpace F] {A : D →ₗ[ℂ] F}
    (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D} {R₁ R₂ : Submodule ℂ (F × F)}
    (h₁ : IsFriedrichsSqExtension A hstab R₁) (h₂ : IsFriedrichsSqExtension A hstab R₂) :
    R₁ = R₂ := by sorry
