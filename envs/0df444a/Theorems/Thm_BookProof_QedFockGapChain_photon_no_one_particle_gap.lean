-- Prove2me | Theorems.Thm_BookProof_QedFockGapChain_photon_no_one_particle_gap
-- name    : BookProof.QedFockGapChain.photon_no_one_particle_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:51:54.634395+00:00
-- url     : https://prove2.me/theorems/11d851df-6b9c-4c6c-b1e0-05b84460799a
-- title:
--   `BookProof.QedFockGapChain.photon_no_one_particle_gap` {p : ℕ → ℝ} (hIR : ∀ ε : ℝ, 0 < ε → ∃ k, |p k| < ε) {m : ℝ} (hm : 0 < m) : ∃ x : finiteModeDomain hermiteBasis, (x :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQedFockGapChain`.
--
--   `BookProof.QedFockGapChain.photon_no_one_particle_gap` {p : ℕ → ℝ} (hIR : ∀ ε : ℝ, 0 < ε → ∃ k, |p k| < ε) {m : ℝ} (hm : 0 < m) : ∃ x : finiteModeDomain hermiteBasis, (x : Lp ℂ 2 (volume : Measure ℝ)) ≠ 0 ∧ quadForm ((finiteModeDomain hermiteBasis).subtype.comp (diagOnePart hermiteBasis (photonDispersion p))) x < m * ‖(x : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.QedFockGapChain.photon_no_one_particle_gap`.

-- Generated from ChapterQedFockGapChain.lean — theorem BookProof.QedFockGapChain.photon_no_one_particle_gap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQedFockGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterTruncationGapLift
open BookProof.HermiteCore
open BookProof.HermiteGalerkin


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FarisLavine
open BookProof.HermiteGalerkin BookProof.HermiteCore
open BookProof.YangMillsFriedrichs
open MeasureTheory
open BookProof.FockDiagonalGapChain


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.QedFockGapChain.photon_no_one_particle_gap {p : ℕ → ℝ} (hIR : ∀ ε : ℝ, 0 < ε → ∃ k, |p k| < ε)
    {m : ℝ} (hm : 0 < m) :
    ∃ x : finiteModeDomain hermiteBasis, (x : Lp ℂ 2 (volume : Measure ℝ)) ≠ 0 ∧
      quadForm ((finiteModeDomain hermiteBasis).subtype.comp
          (diagOnePart hermiteBasis (photonDispersion p))) x
        < m * ‖(x : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2 := by sorry
