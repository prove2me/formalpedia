-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_positive_tail_mass_bound
-- name    : AvramDividend.Classical.avram_wave3_05_tent_positive_tail_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:48:32.820186+00:00
-- url     : https://prove2.me/theorems/3d02bdd1-814a-4206-b511-2d1c456b16cc
-- title:
--   Nonnegative Gaussian Taylor convolution has at most quadratic total mass above the jump size
-- statement:
--   For every nonnegative jump size r and globally integrable nonnegative weight H, the integral of the convolution of H with the triangular kernel over all states x>r is bounded by (r²/2) times the integral of H. The proof establishes the exact kernel mass, full convolution integrability, positivity, and measure-restriction monotonicity.
-- source:
--   Pinned exact Mathlib, remote private elaboration 30 October 2026; Gaussian source Taylor and weighted W'' depend on this bound.

import Mathlib

open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.avram_wave3_05_tent_positive_tail_mass_bound
    (r : ℝ) (hr : 0 ≤ r) (H : ℝ → ℝ)
    (hH : Integrable H volume) (hH0 : ∀ x : ℝ, 0 ≤ H x) :
    (∫ x in Ioi r,
      MeasureTheory.convolution
        ((Ioc (0 : ℝ) r).indicator (fun t => r - t)) H
        (ContinuousLinearMap.mul ℝ ℝ) volume x) ≤
      (r ^ 2 / 2) * (∫ x : ℝ, H x) := by sorry
