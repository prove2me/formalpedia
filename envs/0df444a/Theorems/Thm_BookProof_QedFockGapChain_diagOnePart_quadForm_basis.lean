-- Prove2me | Theorems.Thm_BookProof_QedFockGapChain_diagOnePart_quadForm_basis
-- name    : BookProof.QedFockGapChain.diagOnePart_quadForm_basis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T23:38:20.515562+00:00
-- url     : https://prove2.me/theorems/3d610093-2ef2-455e-8c0f-340169d0679e
-- title:
--   `BookProof.QedFockGapChain.diagOnePart_quadForm_basis` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (k : ℕ) : quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) (modeBasis b k)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQedFockGapChain`.
--
--   `BookProof.QedFockGapChain.diagOnePart_quadForm_basis` (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (k : ℕ) : quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) (modeBasis b k) = w k
--
--   Formalization note: Lean 4 identifier `BookProof.QedFockGapChain.diagOnePart_quadForm_basis`.

-- Generated from ChapterQedFockGapChain.lean — theorem BookProof.QedFockGapChain.diagOnePart_quadForm_basis
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQedFockGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterTruncationGapLift
open BookProof.HermiteGalerkin


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FarisLavine
open BookProof.HermiteGalerkin BookProof.HermiteCore
open BookProof.YangMillsFriedrichs
open MeasureTheory
open BookProof.FockDiagonalGapChain


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.QedFockGapChain.diagOnePart_quadForm_basis (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (k : ℕ) :
    quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) (modeBasis b k) = w k := by sorry
