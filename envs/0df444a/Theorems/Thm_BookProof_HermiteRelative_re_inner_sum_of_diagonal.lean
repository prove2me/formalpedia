-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_re_inner_sum_of_diagonal
-- name    : BookProof.HermiteRelative.re_inner_sum_of_diagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:10:29.000983+00:00
-- url     : https://prove2.me/theorems/6b9ba4e7-9991-4ec7-9943-b507ecc94772
-- title:
--   The Lean 4 theorem `re_inner_sum_of_diagonal` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `re_inner_sum_of_diagonal` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.re_inner_sum_of_diagonal
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
open BookProof.HermiteRelative









open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

theorem BookProof.HermiteRelative.re_inner_sum_of_diagonal (v : ι → E) (hv : Orthonormal ℂ v) (lam : ι → ℝ)
    {D : Submodule ℂ E} (hvD : ∀ a, v a ∈ D) (T : D →ₗ[ℂ] E)
    (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = ((lam a : ℝ) : ℂ) • v a)
    (s : Finset ι) (f : ι → ℂ) (hu : (∑ a ∈ s, f a • v a) ∈ D) :
    (inner ℂ (∑ a ∈ s, f a • v a) (T ⟨∑ a ∈ s, f a • v a, hu⟩) : ℂ).re
      = ∑ a ∈ s, lam a * ‖f a‖ ^ 2 := by sorry
