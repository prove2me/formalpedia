-- Prove2me | Theorems.Thm_BookProof_QedFockGapChain_photonDispersion_nonneg
-- name    : BookProof.QedFockGapChain.photonDispersion_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:44:07.868645+00:00
-- url     : https://prove2.me/theorems/d3d66649-07a8-44a1-9471-57f684d69330
-- title:
--   `BookProof.QedFockGapChain.photonDispersion_nonneg` (p : ℕ → ℝ) (k : ℕ) : 0 ≤ photonDispersion p k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQedFockGapChain`.
--
--   `BookProof.QedFockGapChain.photonDispersion_nonneg` (p : ℕ → ℝ) (k : ℕ) : 0 ≤ photonDispersion p k
--
--   Formalization note: Lean 4 identifier `BookProof.QedFockGapChain.photonDispersion_nonneg`.

-- Generated from ChapterQedFockGapChain.lean — theorem BookProof.QedFockGapChain.photonDispersion_nonneg
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQedFockGapChain
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterTruncationGapLift


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FarisLavine
open BookProof.HermiteGalerkin BookProof.HermiteCore
open BookProof.YangMillsFriedrichs
open MeasureTheory


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.QedFockGapChain.photonDispersion_nonneg (p : ℕ → ℝ) (k : ℕ) : 0 ≤ photonDispersion p k := by sorry
