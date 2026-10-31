-- Prove2me | Theorems.Thm_BookProof_FockDiagonalGapChain_inner_self_ofReal
-- name    : BookProof.FockDiagonalGapChain.inner_self_ofReal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:42:46.134508+00:00
-- url     : https://prove2.me/theorems/cee2a6bf-8a03-4b47-8c55-b4155e4af4e9
-- title:
--   `BookProof.FockDiagonalGapChain.inner_self_ofReal` (v : F) : (inner ℂ v v : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDiagonalGapChain`.
--
--   `BookProof.FockDiagonalGapChain.inner_self_ofReal` (v : F) : (inner ℂ v v : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.FockDiagonalGapChain.inner_self_ofReal`.

-- Generated from ChapterFockDiagonalGapChain.lean — theorem BookProof.FockDiagonalGapChain.inner_self_ofReal
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterScalaronFockGapChain
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterTruncationGapLift


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicQuarticStability BookProof.FockCubicUnbounded
open BookProof.FockInteractionStability
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
open BookProof.HermiteCore
open Module


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FockDiagonalGapChain.inner_self_ofReal (v : F) : (inner ℂ v v : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by sorry
