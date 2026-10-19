-- Prove2me | Theorems.Thm_BookProof_YangMillsFockGapChain_ym_fock_gap_of_nested_ritz_bands
-- name    : BookProof.YangMillsFockGapChain.ym_fock_gap_of_nested_ritz_bands
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:47:52.575311+00:00
-- url     : https://prove2.me/theorems/08d50c12-5f99-4d45-87a7-e6a9b0988d51
-- title:
--   `BookProof.YangMillsFockGapChain.ym_fock_gap_of_nested_ritz_bands` {mu : ℝ} (hmu : 0 ≤ mu) {lo hi : ℕ → ℝ} (hnest : NestedBands lo hi) (hritz : ∀ m, ritzInf (ymHamiltonian (coreRep
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsFockGapChain`.
--
--   `BookProof.YangMillsFockGapChain.ym_fock_gap_of_nested_ritz_bands` {mu : ℝ} (hmu : 0 ≤ mu) {lo hi : ℕ → ℝ} (hnest : NestedBands lo hi) (hritz : ∀ m, ritzInf (ymHamiltonian (coreRepBasis e) fabc) (galerkinSpan (coreBasis e) (m + 1)) ∈ Set.Icc (lo m) (hi m)) {m₀ : ℕ} (hlo : mu ≤ lo m₀) : (∀ m, ritzInf (ymHamiltonian (coreRepBasis e) fabc) (finiteModeDomain (coreBasis e)) ∈ Set.Icc (lo m) (hi m)) ∧ dGamma (ymFockCol e fabc) vac = 0 ∧ ∀ u : FockAlg, u 0 = 0 → mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsFockGapChain.ym_fock_gap_of_nested_ritz_bands`.

-- Generated from ChapterYangMillsFockGapChain.lean — theorem BookProof.YangMillsFockGapChain.ym_fock_gap_of_nested_ritz_bands
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
open BookProof.BandEnclosure
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsHermite
open BookProof.YangMillsFockGapChain


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.FockFieldPerturbation
open BookProof.FarisLavine BookProof.HermiteGalerkin
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.BandEnclosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)

theorem BookProof.YangMillsFockGapChain.ym_fock_gap_of_nested_ritz_bands {mu : ℝ} (hmu : 0 ≤ mu)
    {lo hi : ℕ → ℝ} (hnest : NestedBands lo hi)
    (hritz : ∀ m, ritzInf (ymHamiltonian (coreRepBasis e) fabc)
      (galerkinSpan (coreBasis e) (m + 1)) ∈ Set.Icc (lo m) (hi m))
    {m₀ : ℕ} (hlo : mu ≤ lo m₀) :
    (∀ m, ritzInf (ymHamiltonian (coreRepBasis e) fabc)
        (finiteModeDomain (coreBasis e)) ∈ Set.Icc (lo m) (hi m)) ∧
      dGamma (ymFockCol e fabc) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re := by sorry
