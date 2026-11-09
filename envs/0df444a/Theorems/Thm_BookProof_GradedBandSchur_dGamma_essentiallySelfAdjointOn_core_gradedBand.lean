-- Prove2me | Theorems.Thm_BookProof_GradedBandSchur_dGamma_essentiallySelfAdjointOn_core_gradedBand
-- name    : BookProof.GradedBandSchur.dGamma_essentiallySelfAdjointOn_core_gradedBand
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T16:41:25.443858+00:00
-- url     : https://prove2.me/theorems/170a52f4-6e6e-4b75-a299-97aebdf8ec94
-- title:
--   `BookProof.GradedBandSchur.dGamma_essentiallySelfAdjointOn_core_gradedBand` (hC : 0 ≤ C) (hherm : IsHermCol col) (hcard : ∀ k, (col k).support.card ≤ M) (hband : ∀ k, ∀ j ∈ (col k)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGradedBandSchurEsa`.
--
--   `BookProof.GradedBandSchur.dGamma_essentiallySelfAdjointOn_core_gradedBand` (hC : 0 ≤ C) (hherm : IsHermCol col) (hcard : ∀ k, (col k).support.card ≤ M) (hband : ∀ k, ∀ j ∈ (col k).support, ((deg j : ℤ) - (deg k : ℤ)).natAbs ≤ D) (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp col)
--
--   Formalization note: Lean 4 identifier `BookProof.GradedBandSchur.dGamma_essentiallySelfAdjointOn_core_gradedBand`.

-- Generated from ChapterGradedBandSchurEsa.lean — theorem BookProof.GradedBandSchur.dGamma_essentiallySelfAdjointOn_core_gradedBand
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterQuadraticFockEsa
open BookProof.FockSecondQuantization
open BookProof.GradedBandSchur



open BookProof.FockSecondQuantization BookProof.FockSchur BookProof.FockWeightedSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow

noncomputable section

variable {col : ℕ → (ℕ →₀ ℂ)} {deg : ℕ → ℕ} {D M : ℕ} {C : ℝ}

theorem BookProof.GradedBandSchur.dGamma_essentiallySelfAdjointOn_core_gradedBand (hC : 0 ≤ C) (hherm : IsHermCol col)
    (hcard : ∀ k, (col k).support.card ≤ M)
    (hband : ∀ k, ∀ j ∈ (col k).support, ((deg j : ℤ) - (deg k : ℤ)).natAbs ≤ D)
    (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp col) := by sorry
