-- Prove2me | Theorems.Thm_BookProof_DensitySpectral_density_iff_exists_unitary_diagonal
-- name    : BookProof.DensitySpectral.density_iff_exists_unitary_diagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:56:11.322466+00:00
-- url     : https://prove2.me/theorems/54a8a89c-ab05-4db2-930f-8baa83df448a
-- title:
--   `BookProof.DensitySpectral.density_iff_exists_unitary_diagonal` (ρ : Matrix n n ℂ) : IsDensityMatrix ρ ↔ ∃ (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ), (∀ i, 0 ≤ d i) ∧ (∑ i,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDensitySpectral`.
--
--   `BookProof.DensitySpectral.density_iff_exists_unitary_diagonal` (ρ : Matrix n n ℂ) : IsDensityMatrix ρ ↔ ∃ (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ), (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧ ρ = (U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ d) * (U : Matrix n n ℂ)ᴴ
--
--   Formalization note: Lean 4 identifier `BookProof.DensitySpectral.density_iff_exists_unitary_diagonal`.

-- Generated from ChapterDensitySpectral.lean — theorem BookProof.DensitySpectral.density_iff_exists_unitary_diagonal
import Mathlib
import Definitions.Def_ChapterDensitySpectral
import Definitions.Def_ChapterB4
import Definitions.Def_ChapterDensityMarginalConditional
open BookProof.ChapterB4
open BookProof.DensitySpectral



open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.DensitySpectral.density_iff_exists_unitary_diagonal (ρ : Matrix n n ℂ) :
    IsDensityMatrix ρ ↔
      ∃ (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ),
        (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
        ρ = (U : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ d) * (U : Matrix n n ℂ)ᴴ := by sorry
