-- Prove2me | Theorems.Thm_BookProof_YangMillsFockGapChain_ym_fock_gap_of_field_perturbation
-- name    : BookProof.YangMillsFockGapChain.ym_fock_gap_of_field_perturbation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:47:23.813996+00:00
-- url     : https://prove2.me/theorems/8f4f253a-7e1e-4e42-9fed-2e0b0fb87b89
-- title:
--   `BookProof.YangMillsFockGapChain.ym_fock_gap_of_field_perturbation` {mu : ℝ} (hmu : 0 < mu) (hgap : ∀ x : finiteModeDomain (coreBasis e), mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHami
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsFockGapChain`.
--
--   `BookProof.YangMillsFockGapChain.ym_fock_gap_of_field_perturbation` {mu : ℝ} (hmu : 0 < mu) (hgap : ∀ x : finiteModeDomain (coreBasis e), mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x) {f : ℕ →₀ ℂ} (hf : 2 * l2norm f < mu) {u : FockAlg} (h0 : u 0 = 0) : 0 < mu - 2 * l2norm f ∧ (mu - 2 * l2norm f) * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsFockGapChain.ym_fock_gap_of_field_perturbation`.

-- Generated from ChapterYangMillsFockGapChain.lean — theorem BookProof.YangMillsFockGapChain.ym_fock_gap_of_field_perturbation
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterBandEnclosure
import Mathlib
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
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

theorem BookProof.YangMillsFockGapChain.ym_fock_gap_of_field_perturbation {mu : ℝ} (hmu : 0 < mu)
    (hgap : ∀ x : finiteModeDomain (coreBasis e),
      mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x)
    {f : ℕ →₀ ℂ} (hf : 2 * l2norm f < mu) {u : FockAlg} (h0 : u 0 = 0) :
    0 < mu - 2 * l2norm f ∧
      (mu - 2 * l2norm f) * ‖toLp u‖ ^ 2
        ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re
          + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re := by sorry
