-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_trial_support_subset
-- name    : BookProof.FockCubicUnbounded.trial_support_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:34:45.434988+00:00
-- url     : https://prove2.me/theorems/7ae475b3-2b0c-4ead-bc86-21368a11b6a3
-- title:
--   `BookProof.FockCubicUnbounded.trial_support_subset` (k n : ℕ) (c : ℝ) : (trial k n c).support ⊆ {confAt k n, confAt k (n + 3)}
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.trial_support_subset` (k n : ℕ) (c : ℝ) : (trial k n c).support ⊆ {confAt k n, confAt k (n + 3)}
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.trial_support_subset`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.trial_support_subset
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

theorem BookProof.FockCubicUnbounded.trial_support_subset (k n : ℕ) (c : ℝ) :
    (trial k n c).support ⊆ {confAt k n, confAt k (n + 3)} := by sorry
