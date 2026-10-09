-- Prove2me | Theorems.Thm_BookProof_TensorCore_sectorOp_apply
-- name    : BookProof.TensorCore.sectorOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T09:32:44.228648+00:00
-- url     : https://prove2.me/theorems/6152108a-ab66-4aff-8cba-4bbd091f64f0
-- title:
--   `BookProof.TensorCore.sectorOp_apply` (n : ℕ) (x : sectorDom Hs D₂ n) (x₀ : ((domSpace Hs D₂).pow n)) (hx : (x : Hs.pow n) = inclPow Hs D₂ n x₀) : sectorOp Hs D₂ A n x = derPow Hs
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.sectorOp_apply` (n : ℕ) (x : sectorDom Hs D₂ n) (x₀ : ((domSpace Hs D₂).pow n)) (hx : (x : Hs.pow n) = inclPow Hs D₂ n x₀) : sectorOp Hs D₂ A n x = derPow Hs D₂ A n x₀
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.sectorOp_apply`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.sectorOp_apply
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

theorem BookProof.TensorCore.sectorOp_apply (n : ℕ) (x : sectorDom Hs D₂ n) (x₀ : ((domSpace Hs D₂).pow n))
    (hx : (x : Hs.pow n) = inclPow Hs D₂ n x₀) :
    sectorOp Hs D₂ A n x = derPow Hs D₂ A n x₀ := by sorry
