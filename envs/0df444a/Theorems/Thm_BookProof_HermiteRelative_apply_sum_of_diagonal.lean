-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_apply_sum_of_diagonal
-- name    : BookProof.HermiteRelative.apply_sum_of_diagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:48:44.675115+00:00
-- url     : https://prove2.me/theorems/21702679-7ae9-45f1-a40f-8ed7076d637b
-- title:
--   The Lean 4 theorem `apply_sum_of_diagonal` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `apply_sum_of_diagonal` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.apply_sum_of_diagonal
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

theorem BookProof.HermiteRelative.apply_sum_of_diagonal (v : ι → E) (lam : ι → ℝ) {D : Submodule ℂ E}
    (hvD : ∀ a, v a ∈ D) (T : D →ₗ[ℂ] E)
    (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = ((lam a : ℝ) : ℂ) • v a)
    (s : Finset ι) (f : ι → ℂ) :
    ∀ hu : (∑ a ∈ s, f a • v a) ∈ D,
      T ⟨∑ a ∈ s, f a • v a, hu⟩ = ∑ a ∈ s, (((lam a : ℝ) : ℂ) * f a) • v a := by sorry
