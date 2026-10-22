-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_trial_at_n
-- name    : BookProof.FockCubicUnbounded.trial_at_n
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:34:10.689104+00:00
-- url     : https://prove2.me/theorems/c2fa8178-d545-4ed3-8a9f-884a46a3fbd7
-- title:
--   `BookProof.FockCubicUnbounded.trial_at_n` (k n : ℕ) (c : ℝ) : trial k n c (confAt k n) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.trial_at_n` (k n : ℕ) (c : ℝ) : trial k n c (confAt k n) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.trial_at_n`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.trial_at_n
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterTempleSeparationNecessary
open BookProof.FockSecondQuantization
open BookProof.TempleSeparationNecessary
open BookProof.FockCubicUnbounded


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation

theorem BookProof.FockCubicUnbounded.trial_at_n (k n : ℕ) (c : ℝ) : trial k n c (confAt k n) = 1 := by sorry
