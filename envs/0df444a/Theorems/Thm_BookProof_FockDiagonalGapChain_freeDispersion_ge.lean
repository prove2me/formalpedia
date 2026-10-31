-- Prove2me | Theorems.Thm_BookProof_FockDiagonalGapChain_freeDispersion_ge
-- name    : BookProof.FockDiagonalGapChain.freeDispersion_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:43:29.84856+00:00
-- url     : https://prove2.me/theorems/c7f43fce-bc47-4dbb-bda6-7eeb6838d6e0
-- title:
--   `BookProof.FockDiagonalGapChain.freeDispersion_ge` {m : ℝ} (hm : 0 ≤ m) (p : ℕ → ℝ) (k : ℕ) : m ≤ freeDispersion m p k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockDiagonalGapChain`.
--
--   `BookProof.FockDiagonalGapChain.freeDispersion_ge` {m : ℝ} (hm : 0 ≤ m) (p : ℕ → ℝ) (k : ℕ) : m ≤ freeDispersion m p k
--
--   Formalization note: Lean 4 identifier `BookProof.FockDiagonalGapChain.freeDispersion_ge`.

-- Generated from ChapterFockDiagonalGapChain.lean — theorem BookProof.FockDiagonalGapChain.freeDispersion_ge
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

theorem BookProof.FockDiagonalGapChain.freeDispersion_ge {m : ℝ} (hm : 0 ≤ m) (p : ℕ → ℝ) (k : ℕ) :
    m ≤ freeDispersion m p k := by sorry
