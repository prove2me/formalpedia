-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_moving_base_exponential_polynomial_approx
-- name    : AvramDividend.Classical.avram_wave5_04c_C1_moving_base_exponential_polynomial_approx
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:56:13.663973+00:00
-- url     : https://prove2.me/theorems/c9a31cef-7a19-441f-8a72-7935d4c7065f
-- title:
--   One bounded exponential polynomial uniformly approximates a moving C1 derivative on a finite jump band
-- statement:
--   For any globally C1 Lipschitz real payoff, fixed reserve x, finite negative-jump magnitude band [0,M], and epsilon>0, construct one zero-constant polynomial p and one positive reserve tolerance δ such that p(exp(-r)) approximates w'(b-r) within epsilon uniformly for all r in the band and every base b within δ of x. At the same time, |p(t)|≤L+epsilon on the complete unit interval. The proof combines the Proved continuous derivative compactification, zero-constant Bernstein approximation, and rigorous Heine-Cantor compact-band moving-base uniformity. It supplies a fixed polynomial independent of small time for the actual BV Lévy drift argument.
-- source:
--   Remote compiler candidates/work_on/AvramDividend_04c_C1_moving_base_polynomial_approx_standalone_check.lean; modular candidates/work_on/AvramDividend_04c_C1_moving_base_polynomial_approx_probe.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_derivative_exponential_compactification
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_zero_constant_polynomial_uniform_density
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_derivative_moving_base_uniform_finite_band
set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_C1_moving_base_exponential_polynomial_approx (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧
      (∀ b r : ℝ, |b - x| < δ → r ∈ Icc (0 : ℝ) M →
        |Polynomial.eval (Real.exp (-r)) p - deriv w (b - r)| < ε) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, |Polynomial.eval t p| ≤ L + ε) := by sorry
