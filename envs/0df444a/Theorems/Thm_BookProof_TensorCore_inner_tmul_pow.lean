-- Prove2me | Theorems.Thm_BookProof_TensorCore_inner_tmul_pow
-- name    : BookProof.TensorCore.inner_tmul_pow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:04:47.973365+00:00
-- url     : https://prove2.me/theorems/29991d1b-59d6-45de-95fb-28e1444d6d50
-- title:
--   `BookProof.TensorCore.inner_tmul_pow` (n : ℕ) (x x' : Hs.carrier) (y y' : (Hs.pow n).carrier) : (inner ℂ (x ⊗ₜ[ℂ] y : (Hs.pow (n + 1)).carrier) (x' ⊗ₜ[ℂ] y') : ℂ) = inner ℂ x x' *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.inner_tmul_pow` (n : ℕ) (x x' : Hs.carrier) (y y' : (Hs.pow n).carrier) : (inner ℂ (x ⊗ₜ[ℂ] y : (Hs.pow (n + 1)).carrier) (x' ⊗ₜ[ℂ] y') : ℂ) = inner ℂ x x' * inner ℂ y y'
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.inner_tmul_pow`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.inner_tmul_pow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TensorCore.inner_tmul_pow (n : ℕ) (x x' : Hs.carrier) (y y' : (Hs.pow n).carrier) :
    (inner ℂ (x ⊗ₜ[ℂ] y : (Hs.pow (n + 1)).carrier) (x' ⊗ₜ[ℂ] y') : ℂ)
      = inner ℂ x x' * inner ℂ y y' := by sorry
