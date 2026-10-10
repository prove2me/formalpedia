-- Prove2me | Theorems.Thm_BookProof_KernelBound_kernel_contraction
-- name    : BookProof.KernelBound.kernel_contraction
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:22:00.563243+00:00
-- url     : https://prove2.me/theorems/18a2e93d-27c3-4e9b-8617-082abd4e8e63
-- title:
--   `BookProof.KernelBound.kernel_contraction` (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) (hΨ : ∑ y, ∑ x, ‖Ψ y x‖ ^ 2 = 1) : ∑ y, ‖kernelOp Ψ Φ y‖ ^ 2 ≤ ∑ x, ‖Φ x‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterKernelBound`.
--
--   `BookProof.KernelBound.kernel_contraction` (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜) (hΨ : ∑ y, ∑ x, ‖Ψ y x‖ ^ 2 = 1) : ∑ y, ‖kernelOp Ψ Φ y‖ ^ 2 ≤ ∑ x, ‖Φ x‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.KernelBound.kernel_contraction`.

-- Generated from ChapterKernelBound.lean — theorem BookProof.KernelBound.kernel_contraction
import Mathlib
import Definitions.Def_ChapterKernelBound
open BookProof.KernelBound



open Finset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ιx ιy : Type*} [Fintype ιx] [Fintype ιy]

theorem BookProof.KernelBound.kernel_contraction (Ψ : ιy → ιx → 𝕜) (Φ : ιx → 𝕜)
    (hΨ : ∑ y, ∑ x, ‖Ψ y x‖ ^ 2 = 1) :
    ∑ y, ‖kernelOp Ψ Φ y‖ ^ 2 ≤ ∑ x, ‖Φ x‖ ^ 2 := by sorry
