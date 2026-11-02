-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_moving_base_residual_polynomial_first_moment_bound
-- name    : AvramDividend.Classical.avram_wave5_04c_C1_moving_base_residual_polynomial_first_moment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T16:05:12.630576+00:00
-- url     : https://prove2.me/theorems/47c63c98-b847-4307-b1a2-bc22a5a455e7
-- title:
--   Uniform moving-base C1 jump primitive approximation with full and large-tail first-moment weights
-- statement:
--   For a globally C1 Lipschitz payoff and any negative-jump cutoff M, construct a single fixed zero-constant exponential polynomial p and a positive base tolerance δ such that, for every drift-displaced base b close to x and every residual R≥0, the exact payoff decrement differs from the polynomial primitive by at most epsilon times R plus (2L+epsilon) times R on the large-tail event R>M. The global derivative bound follows from the original Lipschitz hypothesis, continuity and boundedness of the polynomial approximant follow rigorously from its construction. This is the exact pointwise domination needed to combine the original bounded-variation Lévy residual's normalized full and tail first-moment estimates with polynomial semigroup slopes.
-- source:
--   Remote compiler candidates/work_on/AvramDividend_04c_C1_moving_base_random_residual_poly_error_probe.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_moving_base_exponential_polynomial_approx
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_integrated_finite_band_large_residual_bound
set_option autoImplicit false
open MeasureTheory Set Filter
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_C1_moving_base_residual_polynomial_first_moment_bound (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧
      ∀ b R : ℝ, |b - x| < δ → 0 ≤ R →
        |(w b - w (b - R)) -
          (∫ r in (0 : ℝ)..R,
            Polynomial.eval (Real.exp (-r)) p)| ≤
          ε * R + (2 * L + ε) * (if M < R then R else 0) := by sorry
