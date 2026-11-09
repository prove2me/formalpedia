-- Prove2me | Theorems.Thm_BookProof_GradedBandSchur_degW_ge_one
-- name    : BookProof.GradedBandSchur.degW_ge_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T16:40:52.779792+00:00
-- url     : https://prove2.me/theorems/8261446a-21ee-4eb0-b1e5-005a7c69ba39
-- title:
--   `BookProof.GradedBandSchur.degW_ge_one` (deg : ℕ → ℕ) (k : ℕ) : 1 ≤ degW deg k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGradedBandSchurEsa`.
--
--   `BookProof.GradedBandSchur.degW_ge_one` (deg : ℕ → ℕ) (k : ℕ) : 1 ≤ degW deg k
--
--   Formalization note: Lean 4 identifier `BookProof.GradedBandSchur.degW_ge_one`.

-- Generated from ChapterGradedBandSchurEsa.lean — theorem BookProof.GradedBandSchur.degW_ge_one
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

theorem BookProof.GradedBandSchur.degW_ge_one (deg : ℕ → ℕ) (k : ℕ) : 1 ≤ degW deg k := by sorry
