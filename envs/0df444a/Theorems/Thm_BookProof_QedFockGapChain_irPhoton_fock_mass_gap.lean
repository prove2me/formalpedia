-- Prove2me | Theorems.Thm_BookProof_QedFockGapChain_irPhoton_fock_mass_gap
-- name    : BookProof.QedFockGapChain.irPhoton_fock_mass_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:52:13.674356+00:00
-- url     : https://prove2.me/theorems/0759db66-2819-44a5-b361-14c28d40cdfd
-- title:
--   `BookProof.QedFockGapChain.irPhoton_fock_mass_gap` {mu : ℝ} (hmu : 0 < mu) (p : ℕ → ℝ) : (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (dGammaOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQedFockGapChain`.
--
--   `BookProof.QedFockGapChain.irPhoton_fock_mass_gap` {mu : ℝ} (hmu : 0 < mu) (p : ℕ → ℝ) : (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (dGammaOp (opCol hermiteBasis (diagOnePart hermiteBasis (irPhotonDispersion mu p)))) A) ∧ dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (irPhotonDispersion mu p))) vac = 0 ∧ (∀ u : FockAlg, u 0 = 0 → mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (irPhotonDispersion mu p))) u)) : ℂ).re) ∧ ∀ u : FockAlg, u 0 = 0 → u ≠ 0 → 0 < (inner ℂ (toLp u) (toLp (dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (irPhotonDispersion mu p))) u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.QedFockGapChain.irPhoton_fock_mass_gap`.

-- Generated from ChapterQedFockGapChain.lean — theorem BookProof.QedFockGapChain.irPhoton_fock_mass_gap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFockDiagonalGapChain
import Mathlib
import Definitions.Def_ChapterQedFockGapChain
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteCore
open BookProof.YangMillsFriedrichs


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FarisLavine
open BookProof.HermiteGalerkin BookProof.HermiteCore
open BookProof.YangMillsFriedrichs
open MeasureTheory
open BookProof.FockDiagonalGapChain


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.QedFockGapChain.irPhoton_fock_mass_gap {mu : ℝ} (hmu : 0 < mu) (p : ℕ → ℝ) :
    (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
        IsPositiveSelfAdjointExtension
          (dGammaOp (opCol hermiteBasis
            (diagOnePart hermiteBasis (irPhotonDispersion mu p)))) A) ∧
      dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (irPhotonDispersion mu p))) vac
          = 0 ∧
      (∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma
              (opCol hermiteBasis
                (diagOnePart hermiteBasis (irPhotonDispersion mu p))) u)) : ℂ).re) ∧
      ∀ u : FockAlg, u 0 = 0 → u ≠ 0 →
        0 < (inner ℂ (toLp u) (toLp (dGamma
            (opCol hermiteBasis
              (diagOnePart hermiteBasis (irPhotonDispersion mu p))) u)) : ℂ).re := by sorry
