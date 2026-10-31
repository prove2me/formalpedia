-- Prove2me | Theorems.Thm_BookProof_FockDiagonalGapChain_freeField_fock_mass_gap
-- name    : BookProof.FockDiagonalGapChain.freeField_fock_mass_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:43:31.1278+00:00
-- url     : https://prove2.me/theorems/461b6ef0-0bb6-4d08-aaac-524c7673fb2d
-- title:
--   `BookProof.FockDiagonalGapChain.freeField_fock_mass_gap` {m : ℝ} (hm : 0 < m) (p : ℕ → ℝ) : (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (dGamma
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDiagonalGapChain`.
--
--   `BookProof.FockDiagonalGapChain.freeField_fock_mass_gap` {m : ℝ} (hm : 0 < m) (p : ℕ → ℝ) : (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (dGammaOp (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p)))) A) ∧ dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p))) vac = 0 ∧ (∀ u : FockAlg, u 0 = 0 → m * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p))) u)) : ℂ).re) ∧ ∀ u : FockAlg, u 0 = 0 → u ≠ 0 → 0 < (inner ℂ (toLp u) (toLp (dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p))) u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockDiagonalGapChain.freeField_fock_mass_gap`.

-- Generated from ChapterFockDiagonalGapChain.lean — theorem BookProof.FockDiagonalGapChain.freeField_fock_mass_gap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterScalaronFockGapChain
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterTruncationGapLift
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteCore
open BookProof.YangMillsFriedrichs


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicQuarticStability BookProof.FockCubicUnbounded
open BookProof.FockInteractionStability
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
open BookProof.HermiteCore
open Module


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FockDiagonalGapChain.freeField_fock_mass_gap {m : ℝ} (hm : 0 < m) (p : ℕ → ℝ) :
    (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
        IsPositiveSelfAdjointExtension
          (dGammaOp (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p)))) A) ∧
      dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p))) vac = 0 ∧
      (∀ u : FockAlg, u 0 = 0 →
        m * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma
              (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p))) u)) : ℂ).re) ∧
      ∀ u : FockAlg, u 0 = 0 → u ≠ 0 →
        0 < (inner ℂ (toLp u) (toLp (dGamma
            (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p))) u)) : ℂ).re := by sorry
