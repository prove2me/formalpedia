-- Prove2me | Theorems.Thm_BookProof_QedFockGapChain_irPhotonDispersion_ge
-- name    : BookProof.QedFockGapChain.irPhotonDispersion_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:43:42.146482+00:00
-- url     : https://prove2.me/theorems/aa855f80-cec0-43ad-8d06-bba845f37d90
-- title:
--   `BookProof.QedFockGapChain.irPhotonDispersion_ge` (mu : ℝ) (p : ℕ → ℝ) (k : ℕ) : mu ≤ irPhotonDispersion mu p k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQedFockGapChain`.
--
--   `BookProof.QedFockGapChain.irPhotonDispersion_ge` (mu : ℝ) (p : ℕ → ℝ) (k : ℕ) : mu ≤ irPhotonDispersion mu p k
--
--   Formalization note: Lean 4 identifier `BookProof.QedFockGapChain.irPhotonDispersion_ge`.

-- Generated from ChapterQedFockGapChain.lean — theorem BookProof.QedFockGapChain.irPhotonDispersion_ge
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

theorem BookProof.QedFockGapChain.irPhotonDispersion_ge (mu : ℝ) (p : ℕ → ℝ) (k : ℕ) :
    mu ≤ irPhotonDispersion mu p k := by sorry
