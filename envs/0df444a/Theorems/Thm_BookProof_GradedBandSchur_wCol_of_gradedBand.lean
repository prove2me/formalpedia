-- Prove2me | Theorems.Thm_BookProof_GradedBandSchur_wCol_of_gradedBand
-- name    : BookProof.GradedBandSchur.wCol_of_gradedBand
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T16:41:57.076192+00:00
-- url     : https://prove2.me/theorems/83f9540a-8cea-4ea6-8f63-b834880e837e
-- title:
--   `BookProof.GradedBandSchur.wCol_of_gradedBand` (hC : 0 ≤ C) (hherm : IsHermCol col) (hcard : ∀ k, (col k).support.card ≤ M) (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) : WC
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGradedBandSchurEsa`.
--
--   `BookProof.GradedBandSchur.wCol_of_gradedBand` (hC : 0 ≤ C) (hherm : IsHermCol col) (hcard : ∀ k, (col k).support.card ≤ M) (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) : WColBound (degW deg) col (C * M)
--
--   Formalization note: Lean 4 identifier `BookProof.GradedBandSchur.wCol_of_gradedBand`.

-- Generated from ChapterGradedBandSchurEsa.lean — theorem BookProof.GradedBandSchur.wCol_of_gradedBand
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterQuadraticFockEsa
open BookProof.FockSecondQuantization
open BookProof.GradedBandSchur



open BookProof.FockSecondQuantization BookProof.FockSchur BookProof.FockWeightedSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow

noncomputable section

variable {col : ℕ → (ℕ →₀ ℂ)} {deg : ℕ → ℕ} {D M : ℕ} {C : ℝ}

theorem BookProof.GradedBandSchur.wCol_of_gradedBand (hC : 0 ≤ C) (hherm : IsHermCol col)
    (hcard : ∀ k, (col k).support.card ≤ M)
    (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) :
    WColBound (degW deg) col (C * M) := by sorry
