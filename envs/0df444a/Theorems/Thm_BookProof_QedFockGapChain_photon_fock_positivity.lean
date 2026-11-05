-- Prove2me | Theorems.Thm_BookProof_QedFockGapChain_photon_fock_positivity
-- name    : BookProof.QedFockGapChain.photon_fock_positivity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:52:37.937607+00:00
-- url     : https://prove2.me/theorems/157ea974-d359-49d1-8da9-6eadf9722cea
-- title:
--   `BookProof.QedFockGapChain.photon_fock_positivity` (p : ℕ → ℝ) : dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (photonDispersion p))) vac = 0 ∧ ∀ u : FockAlg, u 0 = 0 → (0 :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQedFockGapChain`.
--
--   `BookProof.QedFockGapChain.photon_fock_positivity` (p : ℕ → ℝ) : dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (photonDispersion p))) vac = 0 ∧ ∀ u : FockAlg, u 0 = 0 → (0 : ℝ) * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (photonDispersion p))) u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.QedFockGapChain.photon_fock_positivity`.

-- Generated from ChapterQedFockGapChain.lean — theorem BookProof.QedFockGapChain.photon_fock_positivity
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQedFockGapChain
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteFunctions
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteCore


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FarisLavine
open BookProof.HermiteGalerkin BookProof.HermiteCore
open BookProof.YangMillsFriedrichs
open MeasureTheory
open BookProof.FockDiagonalGapChain


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.QedFockGapChain.photon_fock_positivity (p : ℕ → ℝ) :
    dGamma (opCol hermiteBasis (diagOnePart hermiteBasis (photonDispersion p))) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        (0 : ℝ) * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma
              (opCol hermiteBasis (diagOnePart hermiteBasis (photonDispersion p))) u)) : ℂ).re := by sorry
