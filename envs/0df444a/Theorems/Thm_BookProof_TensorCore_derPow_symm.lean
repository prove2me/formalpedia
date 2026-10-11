-- Prove2me | Theorems.Thm_BookProof_TensorCore_derPow_symm
-- name    : BookProof.TensorCore.derPow_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:05:34.829002+00:00
-- url     : https://prove2.me/theorems/f4d222cd-809c-4162-9a31-98ae7f06263b
-- title:
--   `BookProof.TensorCore.derPow_symm` (hA : SymmetricOn D₂ A) (n : ℕ) : ∀ x y : ((domSpace Hs D₂).pow n), (inner ℂ (derPow Hs D₂ A n x) (inclPow Hs D₂ n y) : ℂ) = inner ℂ (inclPow Hs
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.derPow_symm` (hA : SymmetricOn D₂ A) (n : ℕ) : ∀ x y : ((domSpace Hs D₂).pow n), (inner ℂ (derPow Hs D₂ A n x) (inclPow Hs D₂ n y) : ℂ) = inner ℂ (inclPow Hs D₂ n x) (derPow Hs D₂ A n y)
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.derPow_symm`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.derPow_symm
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

theorem BookProof.TensorCore.derPow_symm (hA : SymmetricOn D₂ A) (n : ℕ) :
    ∀ x y : ((domSpace Hs D₂).pow n),
      (inner ℂ (derPow Hs D₂ A n x) (inclPow Hs D₂ n y) : ℂ)
        = inner ℂ (inclPow Hs D₂ n x) (derPow Hs D₂ A n y) := by sorry
