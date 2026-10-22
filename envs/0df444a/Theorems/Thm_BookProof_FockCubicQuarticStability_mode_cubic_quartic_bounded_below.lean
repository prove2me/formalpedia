-- Prove2me | Theorems.Thm_BookProof_FockCubicQuarticStability_mode_cubic_quartic_bounded_below
-- name    : BookProof.FockCubicQuarticStability.mode_cubic_quartic_bounded_below
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:46:52.974351+00:00
-- url     : https://prove2.me/theorems/69144600-2c87-49ac-b693-0bca2905e310
-- title:
--   `BookProof.FockCubicQuarticStability.mode_cubic_quartic_bounded_below` (k : ℕ) (mu lam : ℝ) (u : FockAlg) : -(2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - mu) ^ 2 / 2) * ‖toLp u‖ ^ 2 ≤ mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicQuarticStability`.
--
--   `BookProof.FockCubicQuarticStability.mode_cubic_quartic_bounded_below` (k : ℕ) (mu lam : ℝ) (u : FockAlg) : -(2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - mu) ^ 2 / 2) * ‖toLp u‖ ^ 2 ≤ mu * ‖toLp (annA k u)‖ ^ 2 + lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicQuarticStability.mode_cubic_quartic_bounded_below`.

-- Generated from ChapterFockCubicQuarticStability.lean — theorem BookProof.FockCubicQuarticStability.mode_cubic_quartic_bounded_below
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicUnbounded
import Mathlib
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.FockCubicQuarticStability


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicUnbounded

theorem BookProof.FockCubicQuarticStability.mode_cubic_quartic_bounded_below (k : ℕ) (mu lam : ℝ) (u : FockAlg) :
    -(2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - mu) ^ 2 / 2) * ‖toLp u‖ ^ 2
      ≤ mu * ‖toLp (annA k u)‖ ^ 2
        + lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
        + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re := by sorry
