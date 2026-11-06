-- Prove2me | Theorems.Thm_BookProof_HermiteLadder_apply_sum_of_shift
-- name    : BookProof.HermiteLadder.apply_sum_of_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T14:46:58.144392+00:00
-- url     : https://prove2.me/theorems/51ffb15f-727e-44cc-8d85-b6cd9fe1cc66
-- title:
--   `BookProof.HermiteLadder.apply_sum_of_shift` (v : ι → E) (σ : ι → ι) (s : ι → ℂ) {D : Submodule ℂ E} (hvD : ∀ a, v a ∈ D) (T : D →ₗ[ℂ] E) (hT : ∀ (a : ι) (h : v a ∈...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteLadderShift`.
--
--   `BookProof.HermiteLadder.apply_sum_of_shift` (v : ι → E) (σ : ι → ι) (s : ι → ℂ) {D : Submodule ℂ E} (hvD : ∀ a, v a ∈ D) (T : D →ₗ[ℂ] E) (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = s a • v (σ a)) (S : Finset ι) (f : ι → ℂ) : ∀ hu : (∑ a ∈ S, f a • v a) ∈ D, T ⟨∑ a ∈ S, f a • v a, hu⟩ = ∑ a ∈ S, (f a * s a) • v (σ a)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteLadder.apply_sum_of_shift`.

-- Generated from ChapterHermiteLadderShift.lean — theorem BookProof.HermiteLadder.apply_sum_of_shift
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterHermiteLadderShift
import Definitions.Def_ChapterHermiteLadderOrder
import Definitions.Def_ChapterHermiteLadderShift
open BookProof.HermiteLadder



open MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QgHermiteOscillator
open BookProof.HyperbolicQuadratic

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

theorem BookProof.HermiteLadder.apply_sum_of_shift (v : ι → E) (σ : ι → ι) (s : ι → ℂ) {D : Submodule ℂ E}
    (hvD : ∀ a, v a ∈ D) (T : D →ₗ[ℂ] E)
    (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = s a • v (σ a))
    (S : Finset ι) (f : ι → ℂ) :
    ∀ hu : (∑ a ∈ S, f a • v a) ∈ D,
      T ⟨∑ a ∈ S, f a • v a, hu⟩ = ∑ a ∈ S, (f a * s a) • v (σ a) := by sorry
