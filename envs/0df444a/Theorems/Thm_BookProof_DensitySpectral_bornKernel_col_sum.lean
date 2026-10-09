-- Prove2me | Theorems.Thm_BookProof_DensitySpectral_bornKernel_col_sum
-- name    : BookProof.DensitySpectral.bornKernel_col_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:55:30.824823+00:00
-- url     : https://prove2.me/theorems/d9dd6758-2e2e-46de-b90c-ab54838e875b
-- title:
--   `BookProof.DensitySpectral.bornKernel_col_sum` (U : Matrix.unitaryGroup n ℂ) (j : n) : ∑ i, bornKernel (U : Matrix n n ℂ) i j = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDensityMarginalConditional`.
--
--   `BookProof.DensitySpectral.bornKernel_col_sum` (U : Matrix.unitaryGroup n ℂ) (j : n) : ∑ i, bornKernel (U : Matrix n n ℂ) i j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.DensitySpectral.bornKernel_col_sum`.

-- Generated from ChapterDensityMarginalConditional.lean — theorem BookProof.DensitySpectral.bornKernel_col_sum
import Mathlib
import Definitions.Def_ChapterDensityMarginalConditional
open BookProof.DensitySpectral



open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.DensitySpectral.bornKernel_col_sum (U : Matrix.unitaryGroup n ℂ) (j : n) :
    ∑ i, bornKernel (U : Matrix n n ℂ) i j = 1 := by sorry
