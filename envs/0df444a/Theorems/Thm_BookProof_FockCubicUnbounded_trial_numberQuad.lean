-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_trial_numberQuad
-- name    : BookProof.FockCubicUnbounded.trial_numberQuad
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:35:29.244052+00:00
-- url     : https://prove2.me/theorems/bc22356e-231e-4fa9-9b59-f852f77ad1d5
-- title:
--   `BookProof.FockCubicUnbounded.trial_numberQuad` (k n : ℕ) (c : ℝ) : numberQuad (trial k n c) = (n : ℝ) + ((n : ℝ) + 3) * c ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.trial_numberQuad` (k n : ℕ) (c : ℝ) : numberQuad (trial k n c) = (n : ℝ) + ((n : ℝ) + 3) * c ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.trial_numberQuad`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.trial_numberQuad
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterTempleSeparationNecessary
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.TempleSeparationNecessary
open BookProof.FockCubicUnbounded


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation

theorem BookProof.FockCubicUnbounded.trial_numberQuad (k n : ℕ) (c : ℝ) :
    numberQuad (trial k n c) = (n : ℝ) + ((n : ℝ) + 3) * c ^ 2 := by sorry
