-- Prove2me | Theorems.Thm_BookProof_FockDiagonalGapChain_diagOnePart_coe
-- name    : BookProof.FockDiagonalGapChain.diagOnePart_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:42:56.253842+00:00
-- url     : https://prove2.me/theorems/323e558e-4484-408e-9fff-a272e7c2a1bb
-- title:
--   `BookProof.FockDiagonalGapChain.diagOnePart_coe` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (x : finiteModeDomain b) : ((diagOnePart b w x : finiteModeDomain b) : F) = ∑ i ∈ ((modeBasis
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDiagonalGapChain`.
--
--   `BookProof.FockDiagonalGapChain.diagOnePart_coe` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (x : finiteModeDomain b) : ((diagOnePart b w x : finiteModeDomain b) : F) = ∑ i ∈ ((modeBasis b).repr x).support, (((w i : ℝ) : ℂ) * ((modeBasis b).repr x i)) • b i
--
--   Formalization note: Lean 4 identifier `BookProof.FockDiagonalGapChain.diagOnePart_coe`.

-- Generated from ChapterFockDiagonalGapChain.lean — theorem BookProof.FockDiagonalGapChain.diagOnePart_coe
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

theorem BookProof.FockDiagonalGapChain.diagOnePart_coe (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (x : finiteModeDomain b) :
    ((diagOnePart b w x : finiteModeDomain b) : F)
      = ∑ i ∈ ((modeBasis b).repr x).support,
          (((w i : ℝ) : ℂ) * ((modeBasis b).repr x i)) • b i := by sorry
