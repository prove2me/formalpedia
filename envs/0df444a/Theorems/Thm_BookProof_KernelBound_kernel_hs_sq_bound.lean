-- Prove2me | Theorems.Thm_BookProof_KernelBound_kernel_hs_sq_bound
-- name    : BookProof.KernelBound.kernel_hs_sq_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:21:25.342975+00:00
-- url     : https://prove2.me/theorems/a0130ebc-5501-4ffb-8daa-9a7c31b7d107
-- title:
--   `BookProof.KernelBound.kernel_hs_sq_bound` (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) : ∑ y, ‖kernelOp Ψ Φ y‖ ^ 2 ≤ (∑ y, ∑ x, ‖Ψ y x‖ ^ 2) * (∑ x, ‖Φ x‖ ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterKernelBound`.
--
--   `BookProof.KernelBound.kernel_hs_sq_bound` (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) : ∑ y, ‖kernelOp Ψ Φ y‖ ^ 2 ≤ (∑ y, ∑ x, ‖Ψ y x‖ ^ 2) * (∑ x, ‖Φ x‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.KernelBound.kernel_hs_sq_bound`.

-- Generated from ChapterKernelBound.lean — theorem BookProof.KernelBound.kernel_hs_sq_bound
import Mathlib
import Definitions.Def_ChapterKernelBound
open BookProof.KernelBound



open Finset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

theorem BookProof.KernelBound.kernel_hs_sq_bound (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) :
    ∑ y, ‖kernelOp Ψ Φ y‖ ^ 2
      ≤ (∑ y, ∑ x, ‖Ψ y x‖ ^ 2) * (∑ x, ‖Φ x‖ ^ 2) := by sorry
