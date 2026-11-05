-- Prove2me | Theorems.Thm_BookProof_HermiteLadder_norm_sum_shift_sq
-- name    : BookProof.HermiteLadder.norm_sum_shift_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T14:46:47.311276+00:00
-- url     : https://prove2.me/theorems/5d7b5132-f899-4452-aaec-2757aee8042c
-- title:
--   `BookProof.HermiteLadder.norm_sum_shift_sq` (v : ι → E) (hv : Orthonormal ℂ v) (σ : ι → ι) (S : Finset ι) (hinj : ∀ a ∈ S, ∀ b ∈ S, σ a = σ b → a = b) (g : ι → ℂ) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteLadderShift`.
--
--   `BookProof.HermiteLadder.norm_sum_shift_sq` (v : ι → E) (hv : Orthonormal ℂ v) (σ : ι → ι) (S : Finset ι) (hinj : ∀ a ∈ S, ∀ b ∈ S, σ a = σ b → a = b) (g : ι → ℂ) : ‖∑ a ∈ S, g a • v (σ a)‖ ^ 2 = ∑ a ∈ S, ‖g a‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteLadder.norm_sum_shift_sq`.

-- Generated from ChapterHermiteLadderShift.lean — theorem BookProof.HermiteLadder.norm_sum_shift_sq
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

theorem BookProof.HermiteLadder.norm_sum_shift_sq (v : ι → E) (hv : Orthonormal ℂ v) (σ : ι → ι) (S : Finset ι)
    (hinj : ∀ a ∈ S, ∀ b ∈ S, σ a = σ b → a = b) (g : ι → ℂ) :
    ‖∑ a ∈ S, g a • v (σ a)‖ ^ 2 = ∑ a ∈ S, ‖g a‖ ^ 2 := by sorry
