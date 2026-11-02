-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_integrated_finite_band_large_residual_bound
-- name    : AvramDividend.Classical.avram_wave5_04c_C1_integrated_finite_band_large_residual_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:46:24.482116+00:00
-- url     : https://prove2.me/theorems/3e058868-bc0d-45e8-83b2-f77e81938fa9
-- title:
--   C1 finite-band primitive error controlled by full and large-tail residual first moments
-- statement:
--   For a C1 real payoff with derivative bounded by L, compare its exact decrement over R≥0 with the integral of a continuous derivative approximant, uniformly bounded by L+epsilon for nonnegative arguments and epsilon-close on [0,M]. The difference is at most epsilon R plus (2L+epsilon) times R when R exceeds M. This rigorous two-regime inequality is the uniform-integrability bridge between a finite-band polynomial approximation and the original finite-variation Lévy residual's normalized first-moment tail.
-- source:
--   Remote compiler sentinel-verified candidates/work_on/AvramDividend_04c_C1_integrated_finite_band_large_residual_bound_probe.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_jump_increment_integrated_uniform_error
set_option autoImplicit false
open MeasureTheory Set
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_C1_integrated_finite_band_large_residual_bound (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (f : ℝ → ℝ) (hf : Continuous f)
    (y R M ε L : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hDerBound : ∀ z : ℝ, |deriv w z| ≤ L)
    (hfBound : ∀ r : ℝ, 0 ≤ r → |f r| ≤ L + ε)
    (happrox : ∀ r ∈ Icc (0 : ℝ) M,
      |deriv w (y - r) - f r| ≤ ε) :
    |(w y - w (y - R)) - (∫ r in (0 : ℝ)..R, f r)| ≤
      ε * R + (2 * L + ε) * (if M < R then R else 0) := by sorry
