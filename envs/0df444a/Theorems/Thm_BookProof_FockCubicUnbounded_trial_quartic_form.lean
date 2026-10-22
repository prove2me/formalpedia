-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_trial_quartic_form
-- name    : BookProof.FockCubicUnbounded.trial_quartic_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:35:36.143334+00:00
-- url     : https://prove2.me/theorems/681ae69b-e4b7-4cba-b679-878f91fe9391
-- title:
--   `BookProof.FockCubicUnbounded.trial_quartic_form` (k n : ℕ) (c : ℝ) : (inner ℂ (toLp (trial k n c)) (toLp (quartA k (trial k n c))) : ℂ).re = (n : ℝ) * ((n : ℝ) - 1) + ((n : ℝ) + 3
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.trial_quartic_form` (k n : ℕ) (c : ℝ) : (inner ℂ (toLp (trial k n c)) (toLp (quartA k (trial k n c))) : ℂ).re = (n : ℝ) * ((n : ℝ) - 1) + ((n : ℝ) + 3) * ((n : ℝ) + 2) * c ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.trial_quartic_form`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.trial_quartic_form
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

theorem BookProof.FockCubicUnbounded.trial_quartic_form (k n : ℕ) (c : ℝ) :
    (inner ℂ (toLp (trial k n c)) (toLp (quartA k (trial k n c))) : ℂ).re
      = (n : ℝ) * ((n : ℝ) - 1) + ((n : ℝ) + 3) * ((n : ℝ) + 2) * c ^ 2 := by sorry
