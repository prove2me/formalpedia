-- Prove2me | Theorems.Thm_BookProof_QedFockGapChain_proca_fock_mass_gap
-- name    : BookProof.QedFockGapChain.proca_fock_mass_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:52:33.629278+00:00
-- url     : https://prove2.me/theorems/aae86b5f-48b1-4aed-93fd-10dbefe6512f
-- title:
--   `BookProof.QedFockGapChain.proca_fock_mass_gap` {m : ℝ} (hm : 0 < m) (p : ℕ → ℝ) : (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (dGammaOp (opCol
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQedFockGapChain`.
--
--   `BookProof.QedFockGapChain.proca_fock_mass_gap` {m : ℝ} (hm : 0 < m) (p : ℕ → ℝ) : (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (dGammaOp (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p)))) A) ∧ dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p))) vac = 0 ∧ (∀ u : FockAlg, u 0 = 0 → m * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p))) u)) : ℂ).re) ∧ ∀ u : FockAlg, u 0 = 0 → u ≠ 0 → 0 < (inner ℂ (toLp u) (toLp (dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (freeDispersion m p))) u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.QedFockGapChain.proca_fock_mass_gap`.

-- Generated from ChapterQedFockGapChain.lean — theorem BookProof.QedFockGapChain.proca_fock_mass_gap
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

theorem BookProof.QedFockGapChain.proca_fock_mass_gap {m : ℝ} (hm : 0 < m) (p : ℕ → ℝ) :
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
