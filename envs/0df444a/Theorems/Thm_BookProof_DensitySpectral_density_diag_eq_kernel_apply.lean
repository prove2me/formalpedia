-- Prove2me | Theorems.Thm_BookProof_DensitySpectral_density_diag_eq_kernel_apply
-- name    : BookProof.DensitySpectral.density_diag_eq_kernel_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:56:26.826983+00:00
-- url     : https://prove2.me/theorems/5f6477d9-08d4-47ee-b3b1-6140e8a381c1
-- title:
--   `BookProof.DensitySpectral.density_diag_eq_kernel_apply` (U : Matrix n n ℂ) (d : n → ℝ) (i : n) : (U * Matrix.diagonal (RCLike.ofReal ∘ d) * Uᴴ : Matrix n n ℂ) i i = ((∑ k, bornKer
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDensityMarginalConditional`.
--
--   `BookProof.DensitySpectral.density_diag_eq_kernel_apply` (U : Matrix n n ℂ) (d : n → ℝ) (i : n) : (U * Matrix.diagonal (RCLike.ofReal ∘ d) * Uᴴ : Matrix n n ℂ) i i = ((∑ k, bornKernel U i k * d k : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.DensitySpectral.density_diag_eq_kernel_apply`.

-- Generated from ChapterDensityMarginalConditional.lean — theorem BookProof.DensitySpectral.density_diag_eq_kernel_apply
import Mathlib
import Definitions.Def_ChapterDensityMarginalConditional
open BookProof.DensitySpectral



open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.DensitySpectral.density_diag_eq_kernel_apply (U : Matrix n n ℂ) (d : n → ℝ) (i : n) :
    (U * Matrix.diagonal (RCLike.ofReal ∘ d) * Uᴴ : Matrix n n ℂ) i i
      = ((∑ k, bornKernel U i k * d k : ℝ) : ℂ) := by sorry
