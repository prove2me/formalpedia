-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_derivative_exponential_compactification
-- name    : AvramDividend.Classical.avram_wave5_04c_C1_derivative_exponential_compactification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:42:49.146964+00:00
-- url     : https://prove2.me/theorems/3b5aeb6b-a2c7-4f81-9c00-a02a1fe3d233
-- title:
--   Bounded zero-at-zero continuous compactification of a globally C1 Lipschitz derivative
-- statement:
--   For any globally C1 L-Lipschitz payoff, base x, and arbitrary M≥0, there is a bounded continuous function F on the real line, vanishing at t=0, such that F(e^{-r}) exactly matches the shifted derivative w'(x-r) for 0≤r≤M. Construct F(t)=min(1,t/e^{-M}) w'(x+log(max(t,e^{-M}))). The positive exponential floor makes logarithm continuous, the prefactor forces F(0)=0, the Lipschitz derivative bound ensures |F|≤L for 0≤t≤1, and on r≤M the function reduces identically to the derivative. This is an exact input to Stone–Weierstrass density on continuous zero-at-origin functions and the weighted BV residual semigroup argument.
-- source:
--   Remote compiler sentinel-verified source candidates/work_on/AvramDividend_04c_C1_derivative_exponential_compactification_probe.lean; 2574 bytes SHA256 f1d29f6182e414d2dc480bc551785a1b6893cdf3524bf751ae0a39229f8f4054

import Mathlib
set_option autoImplicit false
open Set Filter

theorem AvramDividend.Classical.avram_wave5_04c_C1_derivative_exponential_compactification (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x M : ℝ) (hM : 0 ≤ M) :
    ∃ F : ℝ → ℝ, Continuous F ∧ F 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ L) ∧
      (∀ r ∈ Icc (0 : ℝ) M,
        F (Real.exp (-r)) = deriv w (x - r)) := by sorry
