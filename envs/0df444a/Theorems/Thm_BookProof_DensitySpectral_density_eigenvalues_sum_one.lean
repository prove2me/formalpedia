-- Prove2me | Theorems.Thm_BookProof_DensitySpectral_density_eigenvalues_sum_one
-- name    : BookProof.DensitySpectral.density_eigenvalues_sum_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:56:00.195173+00:00
-- url     : https://prove2.me/theorems/ec3350f0-2e39-40be-bacd-0fa03bd86110
-- title:
--   `BookProof.DensitySpectral.density_eigenvalues_sum_one` {ρ : Matrix n n ℂ} (h : IsDensityMatrix ρ) : ∑ i, h.1.eigenvalues i = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDensitySpectral`.
--
--   `BookProof.DensitySpectral.density_eigenvalues_sum_one` {ρ : Matrix n n ℂ} (h : IsDensityMatrix ρ) : ∑ i, h.1.eigenvalues i = 1
--
--   Formalization note: Lean 4 identifier `BookProof.DensitySpectral.density_eigenvalues_sum_one`.

-- Generated from ChapterDensitySpectral.lean — theorem BookProof.DensitySpectral.density_eigenvalues_sum_one
import Mathlib
import Definitions.Def_ChapterDensitySpectral
import Definitions.Def_ChapterB4
import Definitions.Def_ChapterDensityMarginalConditional
open BookProof.ChapterB4
open BookProof.DensitySpectral



open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.DensitySpectral.density_eigenvalues_sum_one {ρ : Matrix n n ℂ} (h : IsDensityMatrix ρ) :
    ∑ i, h.1.eigenvalues i = 1 := by sorry
