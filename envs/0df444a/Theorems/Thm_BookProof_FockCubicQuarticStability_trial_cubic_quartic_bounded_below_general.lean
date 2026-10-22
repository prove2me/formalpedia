-- Prove2me | Theorems.Thm_BookProof_FockCubicQuarticStability_trial_cubic_quartic_bounded_below_general
-- name    : BookProof.FockCubicQuarticStability.trial_cubic_quartic_bounded_below_general
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:47:32.89729+00:00
-- url     : https://prove2.me/theorems/cb7682ff-1d62-4f85-a326-546716282ee8
-- title:
--   `BookProof.FockCubicQuarticStability.trial_cubic_quartic_bounded_below_general` (k : ℕ) (lam : ℝ) (u : FockAlg) : -(2 * lam ^ 4 + lam ^ 2 + 1 / 8) * ‖toLp u‖ ^ 2 ≤ numberQuad u + l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicQuarticStability`.
--
--   `BookProof.FockCubicQuarticStability.trial_cubic_quartic_bounded_below_general` (k : ℕ) (lam : ℝ) (u : FockAlg) : -(2 * lam ^ 4 + lam ^ 2 + 1 / 8) * ‖toLp u‖ ^ 2 ≤ numberQuad u + lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicQuarticStability.trial_cubic_quartic_bounded_below_general`.

-- Generated from ChapterFockCubicQuarticStability.lean — theorem BookProof.FockCubicQuarticStability.trial_cubic_quartic_bounded_below_general
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

theorem BookProof.FockCubicQuarticStability.trial_cubic_quartic_bounded_below_general (k : ℕ) (lam : ℝ) (u : FockAlg) :
    -(2 * lam ^ 4 + lam ^ 2 + 1 / 8) * ‖toLp u‖ ^ 2
      ≤ numberQuad u
        + lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
        + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re := by sorry
