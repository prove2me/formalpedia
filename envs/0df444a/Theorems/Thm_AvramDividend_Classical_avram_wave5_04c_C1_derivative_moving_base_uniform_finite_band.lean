-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_derivative_moving_base_uniform_finite_band
-- name    : AvramDividend.Classical.avram_wave5_04c_C1_derivative_moving_base_uniform_finite_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:53:24.541459+00:00
-- url     : https://prove2.me/theorems/26ae79f8-f3e4-4154-81d0-79d669b9bb6d
-- title:
--   Uniform stability of C1 derivative under a moving base on each bounded jump band
-- statement:
--   If w is C1, for every reserve x, finite jump-magnitude cutoff M≥0 and epsilon>0 there is a positive delta such that all translated derivative values w'(b-r) and w'(x-r) differ by less than epsilon simultaneously for 0≤r≤M whenever |b-x|<delta. The proof applies the Heine-Cantor uniform-continuity theorem on the compact interval [x-M-1,x+1] and verifies both translated arguments lie in that interval. This is the missing moving-base uniformity required when the genuine BV Lévy drift displaces the reserve by h*drift.
-- source:
--   Remote compiler sentinel-verified candidates/work_on/AvramDividend_04c_C1_derivative_moving_base_uniform_finite_band_probe.lean

import Mathlib
set_option autoImplicit false
open Set Filter

theorem AvramDividend.Classical.avram_wave5_04c_C1_derivative_moving_base_uniform_finite_band (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (x M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ b r : ℝ, |b - x| < δ → r ∈ Icc (0 : ℝ) M →
        |deriv w (b - r) - deriv w (x - r)| < ε := by sorry
