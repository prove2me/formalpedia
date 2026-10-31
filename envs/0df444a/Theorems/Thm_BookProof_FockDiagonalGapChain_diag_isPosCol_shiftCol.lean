-- Prove2me | Theorems.Thm_BookProof_FockDiagonalGapChain_diag_isPosCol_shiftCol
-- name    : BookProof.FockDiagonalGapChain.diag_isPosCol_shiftCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:43:05.741278+00:00
-- url     : https://prove2.me/theorems/9f87baf1-57f0-445f-afe9-fbb6789bfdda
-- title:
--   `BookProof.FockDiagonalGapChain.diag_isPosCol_shiftCol` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} (hw : ∀ k, m ≤ w k) : IsPosCol (shiftCol (opCol b (diagOnePart b w)) m)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDiagonalGapChain`.
--
--   `BookProof.FockDiagonalGapChain.diag_isPosCol_shiftCol` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ} (hw : ∀ k, m ≤ w k) : IsPosCol (shiftCol (opCol b (diagOnePart b w)) m)
--
--   Formalization note: Lean 4 identifier `BookProof.FockDiagonalGapChain.diag_isPosCol_shiftCol`.

-- Generated from ChapterFockDiagonalGapChain.lean — theorem BookProof.FockDiagonalGapChain.diag_isPosCol_shiftCol
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
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterTruncationGapLift
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicQuarticStability BookProof.FockCubicUnbounded
open BookProof.FockInteractionStability
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
open BookProof.HermiteCore
open Module


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FockDiagonalGapChain.diag_isPosCol_shiftCol (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ}
    (hw : ∀ k, m ≤ w k) :
    IsPosCol (shiftCol (opCol b (diagOnePart b w)) m) := by sorry
