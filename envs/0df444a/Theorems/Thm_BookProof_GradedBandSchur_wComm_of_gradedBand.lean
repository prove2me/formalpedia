-- Prove2me | Theorems.Thm_BookProof_GradedBandSchur_wComm_of_gradedBand
-- name    : BookProof.GradedBandSchur.wComm_of_gradedBand
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T16:41:16.578726+00:00
-- url     : https://prove2.me/theorems/960dc326-e9d1-4da4-9f8b-12c36decfefd
-- title:
--   `BookProof.GradedBandSchur.wComm_of_gradedBand` (hC : 0 ≤ C) (hcard : ∀ k, (col k).support.card ≤ M) (hband : ∀ k, ∀ j ∈ (col k).support, ((deg j : ℤ) - (deg k : ℤ)).natAbs ≤ D) (h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGradedBandSchurEsa`.
--
--   `BookProof.GradedBandSchur.wComm_of_gradedBand` (hC : 0 ≤ C) (hcard : ∀ k, (col k).support.card ≤ M) (hband : ∀ k, ∀ j ∈ (col k).support, ((deg j : ℤ) - (deg k : ℤ)).natAbs ≤ D) (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) : WCommBound (degW deg) col (C * M * D * (D + 2))
--
--   Formalization note: Lean 4 identifier `BookProof.GradedBandSchur.wComm_of_gradedBand`.

-- Generated from ChapterGradedBandSchurEsa.lean — theorem BookProof.GradedBandSchur.wComm_of_gradedBand
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

theorem BookProof.GradedBandSchur.wComm_of_gradedBand (hC : 0 ≤ C)
    (hcard : ∀ k, (col k).support.card ≤ M)
    (hband : ∀ k, ∀ j ∈ (col k).support, ((deg j : ℤ) - (deg k : ℤ)).natAbs ≤ D)
    (hent : ∀ k j, ‖(col k) j‖ ≤ C * ((deg k : ℝ) + 1)) :
    WCommBound (degW deg) col (C * M * D * (D + 2)) := by sorry
