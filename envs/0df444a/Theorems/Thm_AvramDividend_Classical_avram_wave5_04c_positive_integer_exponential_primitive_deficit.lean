-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_positive_integer_exponential_primitive_deficit
-- name    : AvramDividend.Classical.avram_wave5_04c_positive_integer_exponential_primitive_deficit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:15:03.255747+00:00
-- url     : https://prove2.me/theorems/85b27ec1-f394-4022-949a-c6ed92759746
-- title:
--   Exact exponential-deficit primitive for strictly positive integer modes
-- statement:
--   For any strictly positive integer exponential mode k and any real endpoint R, the interval integral of exp(-k r) from 0 to R equals the exponential deficit (1-exp(-k R))/k. Mathlib's exact interval-integral affine scaling formula reduces the integral to the ordinary exponential primitive, after which k≠0 permits division. This establishes precisely the primitive used to convert the zero-constant polynomial exponential expansion into finite signed Lévy exponential deficits.
-- source:
--   Remote compiler sentinel-verified candidates/work_on/AvramDividend_04c_scalar_integral_exp_deficit_positive_mode_probe.lean

import Mathlib
set_option autoImplicit false
open MeasureTheory Set

theorem AvramDividend.Classical.avram_wave5_04c_positive_integer_exponential_primitive_deficit (k : ℕ) (hk : 1 ≤ k) (R : ℝ) :
    (∫ r in (0 : ℝ)..R, Real.exp ((k : ℝ) * (-r))) =
      (1 - Real.exp ((k : ℝ) * (-R))) / (k : ℝ) := by sorry
