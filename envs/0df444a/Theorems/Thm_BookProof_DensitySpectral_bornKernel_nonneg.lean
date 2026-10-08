-- Prove2me | Theorems.Thm_BookProof_DensitySpectral_bornKernel_nonneg
-- name    : BookProof.DensitySpectral.bornKernel_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:29:42.905976+00:00
-- url     : https://prove2.me/theorems/3c32d934-60e4-4a4a-a1dd-e87fffe9dd84
-- title:
--   `BookProof.DensitySpectral.bornKernel_nonneg` (U : Matrix n n ℂ) (i j : n) : 0 ≤ bornKernel U i j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDensityMarginalConditional`.
--
--   `BookProof.DensitySpectral.bornKernel_nonneg` (U : Matrix n n ℂ) (i j : n) : 0 ≤ bornKernel U i j
--
--   Formalization note: Lean 4 identifier `BookProof.DensitySpectral.bornKernel_nonneg`.

-- Generated from ChapterDensityMarginalConditional.lean — theorem BookProof.DensitySpectral.bornKernel_nonneg
import Mathlib
import Definitions.Def_ChapterDensityMarginalConditional
open BookProof.DensitySpectral



open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]


omit [Fintype n] [DecidableEq n] in

theorem BookProof.DensitySpectral.bornKernel_nonneg (U : Matrix n n ℂ) (i j : n) : 0 ≤ bornKernel U i j := by sorry
