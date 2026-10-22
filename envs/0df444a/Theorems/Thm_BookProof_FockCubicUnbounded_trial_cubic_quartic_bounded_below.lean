-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_trial_cubic_quartic_bounded_below
-- name    : BookProof.FockCubicUnbounded.trial_cubic_quartic_bounded_below
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:35:43.035149+00:00
-- url     : https://prove2.me/theorems/db3c3243-0cc0-48e9-bad6-07cc0b5c3108
-- title:
--   `BookProof.FockCubicUnbounded.trial_cubic_quartic_bounded_below` (k n : ℕ) (hn : 1 ≤ n) (lam c : ℝ) : -(lam ^ 4 / 4 + 2 * lam ^ 2) * ‖toLp (trial k n c)‖ ^ 2 ≤ numberQuad (trial k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.trial_cubic_quartic_bounded_below` (k n : ℕ) (hn : 1 ≤ n) (lam c : ℝ) : -(lam ^ 4 / 4 + 2 * lam ^ 2) * ‖toLp (trial k n c)‖ ^ 2 ≤ numberQuad (trial k n c) + lam * (inner ℂ (toLp (trial k n c)) (toLp (cubeA k (trial k n c))) : ℂ).re + (inner ℂ (toLp (trial k n c)) (toLp (quartA k (trial k n c))) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.trial_cubic_quartic_bounded_below`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.trial_cubic_quartic_bounded_below
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

theorem BookProof.FockCubicUnbounded.trial_cubic_quartic_bounded_below (k n : ℕ) (hn : 1 ≤ n) (lam c : ℝ) :
    -(lam ^ 4 / 4 + 2 * lam ^ 2) * ‖toLp (trial k n c)‖ ^ 2
      ≤ numberQuad (trial k n c)
        + lam * (inner ℂ (toLp (trial k n c)) (toLp (cubeA k (trial k n c))) : ℂ).re
        + (inner ℂ (toLp (trial k n c)) (toLp (quartA k (trial k n c))) : ℂ).re := by sorry
