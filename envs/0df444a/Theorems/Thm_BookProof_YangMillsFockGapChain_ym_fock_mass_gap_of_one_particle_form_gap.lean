-- Prove2me | Theorems.Thm_BookProof_YangMillsFockGapChain_ym_fock_mass_gap_of_one_particle_form_gap
-- name    : BookProof.YangMillsFockGapChain.ym_fock_mass_gap_of_one_particle_form_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:47:30.132997+00:00
-- url     : https://prove2.me/theorems/f1569875-e0f5-473f-a21d-a278e8c58ea4
-- title:
--   `BookProof.YangMillsFockGapChain.ym_fock_mass_gap_of_one_particle_form_gap` {mu : ℝ} (hmu : 0 < mu) (hgap : ∀ x : finiteModeDomain (coreBasis e), mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsFockGapChain`.
--
--   `BookProof.YangMillsFockGapChain.ym_fock_mass_gap_of_one_particle_form_gap` {mu : ℝ} (hmu : 0 < mu) (hgap : ∀ x : finiteModeDomain (coreBasis e), mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x) : (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A) ∧ dGamma (ymFockCol e fabc) vac = 0 ∧ ∀ u : FockAlg, u 0 = 0 → u ≠ 0 → 0 < (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsFockGapChain.ym_fock_mass_gap_of_one_particle_form_gap`.

-- Generated from ChapterYangMillsFockGapChain.lean — theorem BookProof.YangMillsFockGapChain.ym_fock_mass_gap_of_one_particle_form_gap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterBandEnclosure
import Mathlib
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
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

theorem BookProof.YangMillsFockGapChain.ym_fock_mass_gap_of_one_particle_form_gap {mu : ℝ} (hmu : 0 < mu)
    (hgap : ∀ x : finiteModeDomain (coreBasis e),
      mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x) :
    (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
        IsPositiveSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A) ∧
      dGamma (ymFockCol e fabc) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 → u ≠ 0 →
        0 < (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re := by sorry
