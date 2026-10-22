-- Prove2me | Theorems.Thm_BookProof_FockCubicQuarticStability_multiMode_cubic_quartic_bounded_below
-- name    : BookProof.FockCubicQuarticStability.multiMode_cubic_quartic_bounded_below
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:47:30.64378+00:00
-- url     : https://prove2.me/theorems/b4c747b2-c55d-4a35-ba47-a32b28c89116
-- title:
--   `BookProof.FockCubicQuarticStability.multiMode_cubic_quartic_bounded_below` (S : Finset ℕ) {mu lam : ℝ} (hmu : 0 ≤ mu) (u : FockAlg) : -(S.card * (2 * lam ^ 2 + (2 * lam ^ 2 + 1 /
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicQuarticStability`.
--
--   `BookProof.FockCubicQuarticStability.multiMode_cubic_quartic_bounded_below` (S : Finset ℕ) {mu lam : ℝ} (hmu : 0 ≤ mu) (u : FockAlg) : -(S.card * (2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - mu) ^ 2 / 2)) * ‖toLp u‖ ^ 2 ≤ mu * numberQuad u + ∑ k ∈ S, (lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re)
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicQuarticStability.multiMode_cubic_quartic_bounded_below`.

-- Generated from ChapterFockCubicQuarticStability.lean — theorem BookProof.FockCubicQuarticStability.multiMode_cubic_quartic_bounded_below
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

theorem BookProof.FockCubicQuarticStability.multiMode_cubic_quartic_bounded_below (S : Finset ℕ) {mu lam : ℝ} (hmu : 0 ≤ mu)
    (u : FockAlg) :
    -(S.card * (2 * lam ^ 2 + (2 * lam ^ 2 + 1 / 2 - mu) ^ 2 / 2)) * ‖toLp u‖ ^ 2
      ≤ mu * numberQuad u
        + ∑ k ∈ S, (lam * (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
            + (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re) := by sorry
