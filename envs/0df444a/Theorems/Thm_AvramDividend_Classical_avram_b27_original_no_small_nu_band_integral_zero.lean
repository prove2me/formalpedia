-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_nu_band_integral_zero
-- name    : AvramDividend.Classical.avram_b27_original_no_small_nu_band_integral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:19:43.921306+00:00
-- url     : https://prove2.me/theorems/b9b85c69-5c94-4b7d-8a05-d277c0755bbf
-- title:
--   Original Gaussian intrinsic small-negative-mark compensation vanishes if the Levy measure has no small-negative-mark mass
-- statement:
--   For any real measure nu supported away from the original small-negative region (-1,0], each finite band (-1,-1/(n+1)] is nu-null and the integral of the signed jump mark z over that exact original-source band vanishes. This is the deterministic compensator half of the B25 Brownian minus 2N model's claim that the intrinsic compensated small-band martingale is zero.
-- source:
--   Exact original source avram_p4_h_gaussian_intrinsic_small_band_compensated, band Ioc (-1) (-(1/(n+1))), Prove2Me B25 and B27.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_b27_original_no_small_nu_band_integral_zero
    (ν : Measure ℝ)
    (hν : ν (Ioc (-1 : ℝ) 0) = 0)
    (n : ℕ) :
    (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))),
      z ∂ν) = 0 := by sorry
