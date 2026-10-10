-- Prove2me | Theorems.Thm_BookProof_KernelBound_kernel_l2_bound
-- name    : BookProof.KernelBound.kernel_l2_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:22:03.160736+00:00
-- url     : https://prove2.me/theorems/9345e0f4-2c9d-4c9c-8e9e-171e12977794
-- title:
--   `BookProof.KernelBound.kernel_l2_bound` (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) : Real.sqrt (∑ y, ‖kernelOp Ψ Φ y‖ ^ 2) ≤ Real.sqrt (∑ y, ∑ x, ‖Ψ y x‖ ^ 2) * Real.sqrt...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterKernelBound`.
--
--   `BookProof.KernelBound.kernel_l2_bound` (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) : Real.sqrt (∑ y, ‖kernelOp Ψ Φ y‖ ^ 2) ≤ Real.sqrt (∑ y, ∑ x, ‖Ψ y x‖ ^ 2) * Real.sqrt (∑ x, ‖Φ x‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.KernelBound.kernel_l2_bound`.

-- Generated from ChapterKernelBound.lean — theorem BookProof.KernelBound.kernel_l2_bound
import Mathlib
import Definitions.Def_ChapterKernelBound
open BookProof.KernelBound



open Finset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

theorem BookProof.KernelBound.kernel_l2_bound (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) :
    Real.sqrt (∑ y, ‖kernelOp Ψ Φ y‖ ^ 2)
      ≤ Real.sqrt (∑ y, ∑ x, ‖Ψ y x‖ ^ 2) * Real.sqrt (∑ x, ‖Φ x‖ ^ 2) := by sorry
