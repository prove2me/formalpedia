-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_cubic_no_relative_form_bound
-- name    : BookProof.FockCubicUnbounded.cubic_no_relative_form_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:35:10.181882+00:00
-- url     : https://prove2.me/theorems/7715ac1b-c370-46eb-b1a0-2997583360b0
-- title:
--   `BookProof.FockCubicUnbounded.cubic_no_relative_form_bound` (k : ℕ) (a b : ℝ) : ∃ u : FockAlg, u 0 = 0 ∧ a * numberQuad u + b * ‖toLp u‖ ^ 2 < (inner ℂ (toLp u) (toLp (cubeA k u))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.cubic_no_relative_form_bound` (k : ℕ) (a b : ℝ) : ∃ u : FockAlg, u 0 = 0 ∧ a * numberQuad u + b * ‖toLp u‖ ^ 2 < (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.cubic_no_relative_form_bound`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.cubic_no_relative_form_bound
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

theorem BookProof.FockCubicUnbounded.cubic_no_relative_form_bound (k : ℕ) (a b : ℝ) :
    ∃ u : FockAlg, u 0 = 0 ∧
      a * numberQuad u + b * ‖toLp u‖ ^ 2
        < (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re := by sorry
