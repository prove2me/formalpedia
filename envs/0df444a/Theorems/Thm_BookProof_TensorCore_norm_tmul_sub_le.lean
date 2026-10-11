-- Prove2me | Theorems.Thm_BookProof_TensorCore_norm_tmul_sub_le
-- name    : BookProof.TensorCore.norm_tmul_sub_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:04:36.882445+00:00
-- url     : https://prove2.me/theorems/2ae91476-4c85-439f-8da2-c80013194f8a
-- title:
--   `BookProof.TensorCore.norm_tmul_sub_le` {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (x x' : E) (y y' : F) : ‖x ⊗ₜ[ℂ]
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.norm_tmul_sub_le` {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (x x' : E) (y y' : F) : ‖x ⊗ₜ[ℂ] y - x' ⊗ₜ[ℂ] y'‖ ≤ ‖x - x'‖ * ‖y‖ + ‖x'‖ * ‖y - y'‖
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.norm_tmul_sub_le`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.norm_tmul_sub_le
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

theorem BookProof.TensorCore.norm_tmul_sub_le {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (x x' : E) (y y' : F) :
    ‖x ⊗ₜ[ℂ] y - x' ⊗ₜ[ℂ] y'‖ ≤ ‖x - x'‖ * ‖y‖ + ‖x'‖ * ‖y - y'‖ := by sorry
