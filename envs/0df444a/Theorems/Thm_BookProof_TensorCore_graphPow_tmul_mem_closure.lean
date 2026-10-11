-- Prove2me | Theorems.Thm_BookProof_TensorCore_graphPow_tmul_mem_closure
-- name    : BookProof.TensorCore.graphPow_tmul_mem_closure
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:18:08.552207+00:00
-- url     : https://prove2.me/theorems/832f8ce9-ceba-45e0-a349-2a2279cb48cc
-- title:
--   `BookProof.TensorCore.graphPow_tmul_mem_closure` (hcore : IsGraphCore D A) (n : ℕ) (ih : ∀ b : ((domSpace Hs D₂).pow n), graphPow Hs D₂ A n b ∈ (Submodule.map (graphPow Hs D₂ A n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.graphPow_tmul_mem_closure` (hcore : IsGraphCore D A) (n : ℕ) (ih : ∀ b : ((domSpace Hs D₂).pow n), graphPow Hs D₂ A n b ∈ (Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n)).topologicalClosure) (a : D₂) (b : ((domSpace Hs D₂).pow n)) : graphPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b) ∈ (Submodule.map (graphPow Hs D₂ A (n + 1)) (corePow Hs D₂ D (n + 1))).topologicalClosure
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.graphPow_tmul_mem_closure`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.graphPow_tmul_mem_closure
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TensorCore.graphPow_tmul_mem_closure (hcore : IsGraphCore D A) (n : ℕ)
    (ih : ∀ b : ((domSpace Hs D₂).pow n), graphPow Hs D₂ A n b ∈
      (Submodule.map (graphPow Hs D₂ A n) (corePow Hs D₂ D n)).topologicalClosure)
    (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    graphPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b) ∈
      (Submodule.map (graphPow Hs D₂ A (n + 1))
        (corePow Hs D₂ D (n + 1))).topologicalClosure := by sorry
