-- Prove2me | Theorems.Thm_BookProof_DensitySpectral_bornKernel_row_sum
-- name    : BookProof.DensitySpectral.bornKernel_row_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:55:23.051582+00:00
-- url     : https://prove2.me/theorems/89ec652c-de6d-478c-aae0-19bf750e5e5c
-- title:
--   `BookProof.DensitySpectral.bornKernel_row_sum` (U : Matrix.unitaryGroup n ℂ) (i : n) : ∑ j, bornKernel (U : Matrix n n ℂ) i j = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDensityMarginalConditional`.
--
--   `BookProof.DensitySpectral.bornKernel_row_sum` (U : Matrix.unitaryGroup n ℂ) (i : n) : ∑ j, bornKernel (U : Matrix n n ℂ) i j = 1
--
--   Formalization note: Lean 4 identifier `BookProof.DensitySpectral.bornKernel_row_sum`.

-- Generated from ChapterDensityMarginalConditional.lean — theorem BookProof.DensitySpectral.bornKernel_row_sum
import Mathlib
import Definitions.Def_ChapterDensityMarginalConditional
open BookProof.DensitySpectral



open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.DensitySpectral.bornKernel_row_sum (U : Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, bornKernel (U : Matrix n n ℂ) i j = 1 := by sorry
