-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a117_original_gaussian_true_crossing_HJB_separate_variance_clock_bound
-- name    : AvramDividend.Classical.avram_ga_a117_original_gaussian_true_crossing_HJB_separate_variance_clock_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:54:57.154048+00:00
-- url     : https://prove2.me/theorems/9a3f0590-ce8a-469b-83ef-956984486989
-- title:
--   Original Gaussian crossing-cell physical HJB compensation is bounded with separate quadratic-variation and generator clocks
-- statement:
--   For the actual original Gaussian full physical cell, the quadratic-variation subtraction uses variance σ²Δ while the generator drift correction uses Δ. They are different quantities unless σ²=1. If first derivative, half Hessian, and generator coefficients have absolute bounds K, the source-exact HJB residual has absolute size at most K times absolute source increment, increment square, the separate nonnegative variance correction and the separate nonnegative generator clock. This handles the precise physical Gaussian compensator needed to show the genuinely stopped crossing-cell residual is asymptotically small.
-- source:
--   Original Avram Gaussian b0 physical full-source compensated cell with true quadratic variation and generator clock; strengthens proved ga113 which shared one clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a117_original_gaussian_true_crossing_HJB_separate_variance_clock_bound
    (A B C z variance clock K : ℝ) (hK : 0 ≤ K)
    (hv : 0 ≤ variance) (hc : 0 ≤ clock)
    (hA : |A| ≤ K) (hB : |B| ≤ K) (hC : |C| ≤ K) :
    |A * z + B * (z^2 - variance) + clock * C| ≤
      K * (|z| + z^2 + variance + clock) := by sorry
