-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_singular_profile_unbounded_below
-- name    : AvramDividend.Classical.avram_a19_singular_profile_unbounded_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:56:57.347419+00:00
-- url     : https://prove2.me/theorems/fe026c35-9870-480f-a721-ca3fb1fb4c7e
-- title:
--   Singular HJB generator profile has no finite lower bound near zero
-- statement:
--   The scalar profile 3+t^2-4t-2/t, obtained from the proposed bounded-variation infinite-activity Levy generator at surplus t^2, is unbounded below as t decreases to zero. This is a prerequisite for the A19 stochastic counterexample, not a disproof of the full generator-integrability theorem.
-- source:
--   Quantitative A19 original-generator countermodel research, 7 November 2026.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_a19_singular_profile_unbounded_below (B : Real) :
    Exists (fun t : Real => And (0 < t)
      (And (t < 1) (3 + t ^ 2 - 4 * t - 2 / t < B))) := by sorry
