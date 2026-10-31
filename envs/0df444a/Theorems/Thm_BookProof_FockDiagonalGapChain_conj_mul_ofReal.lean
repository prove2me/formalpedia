-- Prove2me | Theorems.Thm_BookProof_FockDiagonalGapChain_conj_mul_ofReal
-- name    : BookProof.FockDiagonalGapChain.conj_mul_ofReal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:42:54.935004+00:00
-- url     : https://prove2.me/theorems/772f5a62-2df4-4427-87a2-9f8704d80055
-- title:
--   `BookProof.FockDiagonalGapChain.conj_mul_ofReal` (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDiagonalGapChain`.
--
--   `BookProof.FockDiagonalGapChain.conj_mul_ofReal` (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.FockDiagonalGapChain.conj_mul_ofReal`.

-- Generated from ChapterFockDiagonalGapChain.lean — theorem BookProof.FockDiagonalGapChain.conj_mul_ofReal
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

theorem BookProof.FockDiagonalGapChain.conj_mul_ofReal (z : ℂ) : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by sorry
