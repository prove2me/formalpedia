-- Prove2me | Theorems.Thm_BookProof_GradedBandSchur_wRow_of_gradedBand
-- name    : BookProof.GradedBandSchur.wRow_of_gradedBand
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T16:40:58.430293+00:00
-- url     : https://prove2.me/theorems/2b45c27b-1218-4b85-bdd5-40e068d619c4
-- title:
--   `BookProof.GradedBandSchur.wRow_of_gradedBand` (hC : 0 ≤ C) (hcard : ∀ k, (col k).support.card ≤ M) (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) : WRowBound (degW deg) col (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGradedBandSchurEsa`.
--
--   `BookProof.GradedBandSchur.wRow_of_gradedBand` (hC : 0 ≤ C) (hcard : ∀ k, (col k).support.card ≤ M) (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) : WRowBound (degW deg) col (C * M)
--
--   Formalization note: Lean 4 identifier `BookProof.GradedBandSchur.wRow_of_gradedBand`.

-- Generated from ChapterGradedBandSchurEsa.lean — theorem BookProof.GradedBandSchur.wRow_of_gradedBand
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterQuadraticFockEsa
open BookProof.GradedBandSchur



open BookProof.FockSecondQuantization BookProof.FockSchur BookProof.FockWeightedSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow

noncomputable section

variable {col : ℕ → (ℕ →₀ ℂ)} {deg : ℕ → ℕ} {D M : ℕ} {C : ℝ}

theorem BookProof.GradedBandSchur.wRow_of_gradedBand (hC : 0 ≤ C)
    (hcard : ∀ k, (col k).support.card ≤ M)
    (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) :
    WRowBound (degW deg) col (C * M) := by sorry
