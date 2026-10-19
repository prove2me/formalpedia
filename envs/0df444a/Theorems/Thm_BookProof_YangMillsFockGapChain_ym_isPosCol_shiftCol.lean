-- Prove2me | Theorems.Thm_BookProof_YangMillsFockGapChain_ym_isPosCol_shiftCol
-- name    : BookProof.YangMillsFockGapChain.ym_isPosCol_shiftCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:47:24.989014+00:00
-- url     : https://prove2.me/theorems/9bc0dd2a-b123-431e-9a62-eaef23cb0429
-- title:
--   `BookProof.YangMillsFockGapChain.ym_isPosCol_shiftCol` {mu : ℝ} (hgap : ∀ x : finiteModeDomain (coreBasis e), mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fab
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsFockGapChain`.
--
--   `BookProof.YangMillsFockGapChain.ym_isPosCol_shiftCol` {mu : ℝ} (hgap : ∀ x : finiteModeDomain (coreBasis e), mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x) : IsPosCol (shiftCol (ymFockCol e fabc) mu)
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsFockGapChain.ym_isPosCol_shiftCol`.

-- Generated from ChapterYangMillsFockGapChain.lean — theorem BookProof.YangMillsFockGapChain.ym_isPosCol_shiftCol
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

theorem BookProof.YangMillsFockGapChain.ym_isPosCol_shiftCol {mu : ℝ}
    (hgap : ∀ x : finiteModeDomain (coreBasis e),
      mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x) :
    IsPosCol (shiftCol (ymFockCol e fabc) mu) := by sorry
