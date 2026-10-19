-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_eq_frExt_of_isSelfAdjointExtension
-- name    : BookProof.FriedrichsSquare.eq_frExt_of_isSelfAdjointExtension
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T00:42:02.063998+00:00
-- url     : https://prove2.me/theorems/b1c2c534-ec51-4713-9b99-6d9fc4307c2f
-- title:
--   `BookProof.FriedrichsSquare.eq_frExt_of_isSelfAdjointExtension` [CompleteSpace F] {A : D →ₗ[ℂ] F} (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.eq_frExt_of_isSelfAdjointExtension` [CompleteSpace F] {A : D →ₗ[ℂ] F} (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D} {Dom : Submodule ℂ F} {B : Dom →ₗ[ℂ] F} (hB : IsSelfAdjointExtension (sqOp A hstab) B) (hdomle : Dom ≤ clDom A) : Dom = frDom A ∧ ∀ (x : F) (h₁ : x ∈ Dom) (h₂ : x ∈ frDom A), B ⟨x, h₁⟩ = frExt A hdense hsym ⟨x, h₂⟩
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.eq_frExt_of_isSelfAdjointExtension`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.eq_frExt_of_isSelfAdjointExtension
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
open BookProof.ClosureUniqueness
open BookProof.EsaClosure
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.FriedrichsSquare.eq_frExt_of_isSelfAdjointExtension [CompleteSpace F] {A : D →ₗ[ℂ] F}
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D}
    {Dom : Submodule ℂ F} {B : Dom →ₗ[ℂ] F} (hB : IsSelfAdjointExtension (sqOp A hstab) B)
    (hdomle : Dom ≤ clDom A) :
    Dom = frDom A ∧ ∀ (x : F) (h₁ : x ∈ Dom) (h₂ : x ∈ frDom A),
      B ⟨x, h₁⟩ = frExt A hdense hsym ⟨x, h₂⟩ := by sorry
