-- Prove2me | Theorems.Thm_BookProof_QuadFockEsa_gradedBand_of_isBand2
-- name    : BookProof.QuadFockEsa.gradedBand_of_isBand2
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T21:07:29.073757+00:00
-- url     : https://prove2.me/theorems/36b1f1cf-0d0a-45ed-b418-8c55a66f42c4
-- title:
--   `BookProof.QuadFockEsa.gradedBand_of_isBand2` (e : ℕ ≃ (Fin d →₀ ℕ)) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (h : IsBand2 T) : ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ (∀ k,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuadraticFockEsa`.
--
--   `BookProof.QuadFockEsa.gradedBand_of_isBand2` (e : ℕ ≃ (Fin d →₀ ℕ)) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (h : IsBand2 T) : ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ (∀ k, (hermCol e T k).support.card ≤ M) ∧ (∀ k, ∀ j ∈ (hermCol e T k).support, (((e j).degree : ℤ) - ((e k).degree : ℤ)).natAbs ≤ 2) ∧ (∀ k j, ‖hermCol e T k j‖ ≤ C * (((e k).degree : ℝ) + 1))
--
--   Formalization note: Lean 4 identifier `BookProof.QuadFockEsa.gradedBand_of_isBand2`.

-- Generated from ChapterQuadraticFockEsa.lean — theorem BookProof.QuadFockEsa.gradedBand_of_isBand2
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterGradedBandSchurEsa
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterQuadraticFockEsa
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterQuadraticFockEsa
open BookProof.HermiteBand
open BookProof.QuadFockEsa



open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.GradedBandSchur
open BookProof.FockSecondQuantization BookProof.NavierStokesFlow
open BookProof.HermiteGalerkin BookProof.FarisLavine
open BookProof.YangMillsHermite BookProof.FullQuadratic
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadFockEsa.gradedBand_of_isBand2 (e : ℕ ≃ (Fin d →₀ ℕ))
    {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (h : IsBand2 T) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      (∀ k, (hermCol e T k).support.card ≤ M) ∧
      (∀ k, ∀ j ∈ (hermCol e T k).support,
        (((e j).degree : ℤ) - ((e k).degree : ℤ)).natAbs ≤ 2) ∧
      (∀ k j, ‖hermCol e T k j‖ ≤ C * (((e k).degree : ℝ) + 1)) := by sorry
