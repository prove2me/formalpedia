-- Prove2me | Theorems.Thm_BookProof_YangMillsFockGapChain_isPosCol_shiftCol_opCol_of_form_gap
-- name    : BookProof.YangMillsFockGapChain.isPosCol_shiftCol_opCol_of_form_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:46:34.100988+00:00
-- url     : https://prove2.me/theorems/9ac41757-28e3-44ea-a80b-336703385998
-- title:
--   `BookProof.YangMillsFockGapChain.isPosCol_shiftCol_opCol_of_form_gap` (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) {mu : ℝ} (hgap : ∀ x : finiteModeDo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsFockGapChain`.
--
--   `BookProof.YangMillsFockGapChain.isPosCol_shiftCol_opCol_of_form_gap` (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) {mu : ℝ} (hgap : ∀ x : finiteModeDomain b, mu * ‖(x : F)‖ ^ 2 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) : IsPosCol (shiftCol (opCol b A) mu)
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsFockGapChain.isPosCol_shiftCol_opCol_of_form_gap`.

-- Generated from ChapterYangMillsFockGapChain.lean — theorem BookProof.YangMillsFockGapChain.isPosCol_shiftCol_opCol_of_form_gap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterBandEnclosure
import Mathlib
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.YangMillsFockGapChain


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.FockFieldPerturbation
open BookProof.FarisLavine BookProof.HermiteGalerkin
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.BandEnclosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFockGapChain.isPosCol_shiftCol_opCol_of_form_gap (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) {mu : ℝ}
    (hgap : ∀ x : finiteModeDomain b,
      mu * ‖(x : F)‖ ^ 2 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    IsPosCol (shiftCol (opCol b A) mu) := by sorry
