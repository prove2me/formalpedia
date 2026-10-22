-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_trial_at_n3
-- name    : BookProof.FockCubicUnbounded.trial_at_n3
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:34:18.183963+00:00
-- url     : https://prove2.me/theorems/0a38cd1c-dbe8-47a3-bba5-65972c5018cd
-- title:
--   `BookProof.FockCubicUnbounded.trial_at_n3` (k n : ℕ) (c : ℝ) : trial k n c (confAt k (n + 3)) = ((c : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.trial_at_n3` (k n : ℕ) (c : ℝ) : trial k n c (confAt k (n + 3)) = ((c : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.trial_at_n3`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.trial_at_n3
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

theorem BookProof.FockCubicUnbounded.trial_at_n3 (k n : ℕ) (c : ℝ) :
    trial k n c (confAt k (n + 3)) = ((c : ℝ) : ℂ) := by sorry
