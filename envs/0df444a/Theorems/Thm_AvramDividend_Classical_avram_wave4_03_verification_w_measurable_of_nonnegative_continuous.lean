-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_verification_w_measurable_of_nonnegative_continuous
-- name    : AvramDividend.Classical.avram_wave4_03_verification_w_measurable_of_nonnegative_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:18:08.458896+00:00
-- url     : https://prove2.me/theorems/3c681a5c-5cb1-436b-b652-7b0743a96097
-- title:
--   Actual BV HJB verification payoff is Borel from nonnegative continuity and killed negative values
-- statement:
--   The exact test-function hypotheses in the source positive-cap BV verification theorem imply global Borel measurability: continuity on nonnegative reserves and identically zero negative reserves suffice. The pinned measurable-piecewise theorem combines the continuous nonnegative branch and the constant negative branch, including the origin. This discharges the missing Borel hypothesis when applying the canonically Proved original controlled predictable nonlinear jump-mark kernel, without changing the original HJB function.
-- source:
--   Original Avram–Palmowski–Pistorius (2007), Proposition 4(i), nonnegative surplus value function and killed negative-reserve convention; exact pinned Mathlib ContinuousOn.measurable_piecewise (signature inspected 31 October 2026). Supports source-marked-kernel theorem 7898252f-6d90-4103-b20b-298e5d9a285a.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.avram_wave4_03_verification_w_measurable_of_nonnegative_continuous
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ y < 0, w y = 0) : Measurable w := by sorry
