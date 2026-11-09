-- Prove2me | Theorems.Thm_BookProof_GradedBandSchur_degW_pos
-- name    : BookProof.GradedBandSchur.degW_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T16:40:49.45587+00:00
-- url     : https://prove2.me/theorems/ce1e8d50-f506-4620-a036-4abbb07d33ca
-- title:
--   `BookProof.GradedBandSchur.degW_pos` (deg : ℕ → ℕ) (k : ℕ) : 0 < degW deg k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGradedBandSchurEsa`.
--
--   `BookProof.GradedBandSchur.degW_pos` (deg : ℕ → ℕ) (k : ℕ) : 0 < degW deg k
--
--   Formalization note: Lean 4 identifier `BookProof.GradedBandSchur.degW_pos`.

-- Generated from ChapterGradedBandSchurEsa.lean — theorem BookProof.GradedBandSchur.degW_pos
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

theorem BookProof.GradedBandSchur.degW_pos (deg : ℕ → ℕ) (k : ℕ) : 0 < degW deg k := by sorry
