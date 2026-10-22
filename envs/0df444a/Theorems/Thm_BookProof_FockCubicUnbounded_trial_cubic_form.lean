-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_trial_cubic_form
-- name    : BookProof.FockCubicUnbounded.trial_cubic_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:35:38.358353+00:00
-- url     : https://prove2.me/theorems/7de5faab-881f-4333-b05f-50b808bf9e22
-- title:
--   `BookProof.FockCubicUnbounded.trial_cubic_form` (k n : ℕ) (hn : 1 ≤ n) (c : ℝ) : (inner ℂ (toLp (trial k n c)) (toLp (cubeA k (trial k n c))) : ℂ).re = 2 * c * (Real.sqrt (((n : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.trial_cubic_form` (k n : ℕ) (hn : 1 ≤ n) (c : ℝ) : (inner ℂ (toLp (trial k n c)) (toLp (cubeA k (trial k n c))) : ℂ).re = 2 * c * (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)))
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.trial_cubic_form`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.trial_cubic_form
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

theorem BookProof.FockCubicUnbounded.trial_cubic_form (k n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    (inner ℂ (toLp (trial k n c)) (toLp (cubeA k (trial k n c))) : ℂ).re
      = 2 * c * (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) := by sorry
