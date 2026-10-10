-- Prove2me | Theorems.Thm_BookProof_KernelBound_kernel_row_bound
-- name    : BookProof.KernelBound.kernel_row_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:21:50.743323+00:00
-- url     : https://prove2.me/theorems/4bd76190-e904-40d8-8d25-fa77e7f361d8
-- title:
--   `BookProof.KernelBound.kernel_row_bound` (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) (y : ιy) : ‖kernelOp Ψ Φ y‖ ^ 2 ≤ (∑ x, ‖Ψ y x‖ ^ 2) * (∑ x, ‖Φ x‖ ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterKernelBound`.
--
--   `BookProof.KernelBound.kernel_row_bound` (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) (y : ιy) : ‖kernelOp Ψ Φ y‖ ^ 2 ≤ (∑ x, ‖Ψ y x‖ ^ 2) * (∑ x, ‖Φ x‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.KernelBound.kernel_row_bound`.

-- Generated from ChapterKernelBound.lean — theorem BookProof.KernelBound.kernel_row_bound
import Mathlib
import Definitions.Def_ChapterKernelBound
open BookProof.KernelBound



open Finset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

theorem BookProof.KernelBound.kernel_row_bound (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) (y : ιy) :
    ‖kernelOp Ψ Φ y‖ ^ 2 ≤ (∑ x, ‖Ψ y x‖ ^ 2) * (∑ x, ‖Φ x‖ ^ 2) := by sorry
