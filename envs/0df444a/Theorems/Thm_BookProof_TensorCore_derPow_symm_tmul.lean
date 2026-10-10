-- Prove2me | Theorems.Thm_BookProof_TensorCore_derPow_symm_tmul
-- name    : BookProof.TensorCore.derPow_symm_tmul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:51:20.702539+00:00
-- url     : https://prove2.me/theorems/bef7c972-3f22-485d-ad76-57e2ef53bbda
-- title:
--   `BookProof.TensorCore.derPow_symm_tmul` (hA : SymmetricOn D₂ A) (n : ℕ) (ih : ∀ x y : ((domSpace Hs D₂).pow n), (inner ℂ (derPow Hs D₂ A n x) (inclPow Hs D₂ n y) : ℂ) = inner ℂ (in
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.derPow_symm_tmul` (hA : SymmetricOn D₂ A) (n : ℕ) (ih : ∀ x y : ((domSpace Hs D₂).pow n), (inner ℂ (derPow Hs D₂ A n x) (inclPow Hs D₂ n y) : ℂ) = inner ℂ (inclPow Hs D₂ n x) (derPow Hs D₂ A n y)) (a c : D₂) (b d : ((domSpace Hs D₂).pow n)) : (inner ℂ (derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)) (inclPow Hs D₂ (n + 1) (c ⊗ₜ[ℂ] d)) : ℂ) = inner ℂ (inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b)) (derPow Hs D₂ A (n + 1) (c ⊗ₜ[ℂ] d))
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.derPow_symm_tmul`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.derPow_symm_tmul
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterFarisLavineCore
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TensorCore.derPow_symm_tmul (hA : SymmetricOn D₂ A) (n : ℕ)
    (ih : ∀ x y : ((domSpace Hs D₂).pow n),
      (inner ℂ (derPow Hs D₂ A n x) (inclPow Hs D₂ n y) : ℂ)
        = inner ℂ (inclPow Hs D₂ n x) (derPow Hs D₂ A n y))
    (a c : D₂) (b d : ((domSpace Hs D₂).pow n)) :
    (inner ℂ (derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)) (inclPow Hs D₂ (n + 1) (c ⊗ₜ[ℂ] d)) : ℂ)
      = inner ℂ (inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b)) (derPow Hs D₂ A (n + 1) (c ⊗ₜ[ℂ] d)) := by sorry
