-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_trial_at_other
-- name    : BookProof.FockCubicUnbounded.trial_at_other
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:34:58.77986+00:00
-- url     : https://prove2.me/theorems/72e91270-9970-4ffe-8e07-8b4f74191155
-- title:
--   `BookProof.FockCubicUnbounded.trial_at_other` {k n : ℕ} {c : ℝ} {m : ℕ} (h1 : m ≠ n) (h2 : m ≠ n + 3) : trial k n c (confAt k m) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.trial_at_other` {k n : ℕ} {c : ℝ} {m : ℕ} (h1 : m ≠ n) (h2 : m ≠ n + 3) : trial k n c (confAt k m) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.trial_at_other`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.trial_at_other
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

theorem BookProof.FockCubicUnbounded.trial_at_other {k n : ℕ} {c : ℝ} {m : ℕ} (h1 : m ≠ n) (h2 : m ≠ n + 3) :
    trial k n c (confAt k m) = 0 := by sorry
