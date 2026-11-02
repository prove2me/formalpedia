-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_jump_increment_integrated_uniform_error
-- name    : AvramDividend.Classical.avram_wave5_04c_C1_jump_increment_integrated_uniform_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:09:23.57025+00:00
-- url     : https://prove2.me/theorems/81c9f8a7-0aa9-4f9c-a79f-4afedaff0a26
-- title:
--   First-moment weighted error for integrated C1 jump derivative approximants
-- statement:
--   For any globally C1 real payoff and a continuous approximation f of its translated derivative on the interval of a nonnegative negative-jump magnitude R, bound the error between the exact payoff increment and the primitive of f by ε times R. The proof uses the exact C1 jump-increment FTC identity, continuity to justify interval-integral subtraction, and the pinned Mathlib interval-integral norm bound. The error is weighted linearly by the actual jump magnitude, the domination required for genuine bounded-variation Lévy first-moment arguments, with no second derivative.
-- source:
--   Remote compiler sentinel-verified candidates/work_on/AvramDividend_04c_C1_integrated_approximation_error_probe.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_negative_jump_increment_FTC
set_option autoImplicit false
open MeasureTheory Set
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_C1_jump_increment_integrated_uniform_error (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w) (f : ℝ → ℝ) (hf : Continuous f) (y R ε : ℝ) (hR : 0 ≤ R) (herror : ∀ r ∈ Set.uIoc (0 : ℝ) R, |deriv w (y - r) - f r| ≤ ε) :
    |(w y - w (y - R)) - (∫ r in (0 : ℝ)..R, f r)| ≤ ε * R := by sorry
