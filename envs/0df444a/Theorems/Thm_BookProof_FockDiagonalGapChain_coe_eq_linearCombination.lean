-- Prove2me | Theorems.Thm_BookProof_FockDiagonalGapChain_coe_eq_linearCombination
-- name    : BookProof.FockDiagonalGapChain.coe_eq_linearCombination
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:42:49.66848+00:00
-- url     : https://prove2.me/theorems/1e746bed-5286-4c55-9956-4a5182cedabb
-- title:
--   `BookProof.FockDiagonalGapChain.coe_eq_linearCombination` (b : HilbertBasis ℕ ℂ F) (x : finiteModeDomain b) : (x : F) = Finsupp.linearCombination ℂ (⇑b) ((modeBasis b).repr x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDiagonalGapChain`.
--
--   `BookProof.FockDiagonalGapChain.coe_eq_linearCombination` (b : HilbertBasis ℕ ℂ F) (x : finiteModeDomain b) : (x : F) = Finsupp.linearCombination ℂ (⇑b) ((modeBasis b).repr x)
--
--   Formalization note: Lean 4 identifier `BookProof.FockDiagonalGapChain.coe_eq_linearCombination`.

-- Generated from ChapterFockDiagonalGapChain.lean — theorem BookProof.FockDiagonalGapChain.coe_eq_linearCombination
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
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterTruncationGapLift
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

theorem BookProof.FockDiagonalGapChain.coe_eq_linearCombination (b : HilbertBasis ℕ ℂ F) (x : finiteModeDomain b) :
    (x : F) = Finsupp.linearCombination ℂ (⇑b) ((modeBasis b).repr x) := by sorry
