-- Prove2me | Theorems.Thm_BookProof_FockDiagonalGapChain_diagOnePart_inner
-- name    : BookProof.FockDiagonalGapChain.diagOnePart_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:43:07.516598+00:00
-- url     : https://prove2.me/theorems/56b7201d-35b8-4601-b478-17cfa2162b02
-- title:
--   `BookProof.FockDiagonalGapChain.diagOnePart_inner` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (x y : finiteModeDomain b) : (inner ℂ (x : F) ((diagOnePart b w y : finiteModeDomain b) : F)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDiagonalGapChain`.
--
--   `BookProof.FockDiagonalGapChain.diagOnePart_inner` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (x y : finiteModeDomain b) : (inner ℂ (x : F) ((diagOnePart b w y : finiteModeDomain b) : F) : ℂ) = ∑ i ∈ ((modeBasis b).repr y).support, ((w i : ℝ) : ℂ) * (starRingEnd ℂ ((modeBasis b).repr x i)) * ((modeBasis b).repr y i)
--
--   Formalization note: Lean 4 identifier `BookProof.FockDiagonalGapChain.diagOnePart_inner`.

-- Generated from ChapterFockDiagonalGapChain.lean — theorem BookProof.FockDiagonalGapChain.diagOnePart_inner
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

theorem BookProof.FockDiagonalGapChain.diagOnePart_inner (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (x y : finiteModeDomain b) :
    (inner ℂ (x : F) ((diagOnePart b w y : finiteModeDomain b) : F) : ℂ)
      = ∑ i ∈ ((modeBasis b).repr y).support,
          ((w i : ℝ) : ℂ) * (starRingEnd ℂ ((modeBasis b).repr x i)) *
            ((modeBasis b).repr y i) := by sorry
