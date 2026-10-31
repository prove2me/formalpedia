-- Prove2me | Theorems.Thm_BookProof_FockDiagonalGapChain_diagOnePart_quadForm_ge
-- name    : BookProof.FockDiagonalGapChain.diagOnePart_quadForm_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:42:58.673952+00:00
-- url     : https://prove2.me/theorems/04c1c1c2-d8df-43c1-88ed-392e8e560df3
-- title:
--   `BookProof.FockDiagonalGapChain.diagOnePart_quadForm_ge` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} (hw : ∀ k, m ≤ w k) (x : finiteModeDomain b) : m * ‖(x : F)‖ ^ 2 ≤...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDiagonalGapChain`.
--
--   `BookProof.FockDiagonalGapChain.diagOnePart_quadForm_ge` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} (hw : ∀ k, m ≤ w k) (x : finiteModeDomain b) : m * ‖(x : F)‖ ^ 2 ≤ quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) x
--
--   Formalization note: Lean 4 identifier `BookProof.FockDiagonalGapChain.diagOnePart_quadForm_ge`.

-- Generated from ChapterFockDiagonalGapChain.lean — theorem BookProof.FockDiagonalGapChain.diagOnePart_quadForm_ge
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterScalaronFockGapChain
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterTruncationGapLift
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicQuarticStability BookProof.FockCubicUnbounded
open BookProof.FockInteractionStability
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
open BookProof.HermiteCore
open Module


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FockDiagonalGapChain.diagOnePart_quadForm_ge (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ}
    (hw : ∀ k, m ≤ w k) (x : finiteModeDomain b) :
    m * ‖(x : F)‖ ^ 2
      ≤ quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) x := by sorry
