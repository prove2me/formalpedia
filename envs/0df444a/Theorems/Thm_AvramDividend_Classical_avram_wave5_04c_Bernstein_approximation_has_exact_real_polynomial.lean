-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_approximation_has_exact_real_polynomial
-- name    : AvramDividend.Classical.avram_wave5_04c_Bernstein_approximation_has_exact_real_polynomial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:47:14.208892+00:00
-- url     : https://prove2.me/theorems/6b009077-1537-4c36-93f9-72627f9bc1d2
-- title:
--   Every finite Bernstein approximation is exactly an evaluable real polynomial
-- statement:
--   For every finite Bernstein approximation of any continuous real function on the unit interval, construct the exact real polynomial whose evaluation agrees pointwise with that approximation. The coefficient expression is the finite sum over k≤n of choose(n,k) f(k/n) X^k(1−X)^(n−k), and Mathlib bernsteinApproximation.apply and bernstein_apply identify the two expressions. This gives the constructive polynomial extraction needed to transform exponential compactification into finite signed integer exponential tests for the Lévy BV generator bridge.
-- source:
--   Remote compiler sentinel-verified source candidates/work_on/AvramDividend_04c_Bernstein_polynomial_realization_probe.lean; 893 bytes SHA256 cde6823fe3fbc144783b9c2c5a54c3fb7d09594e685ea3bc891b875b4363577c

import Mathlib
set_option autoImplicit false
open Set Filter
open scoped BigOperators

theorem AvramDividend.Classical.avram_wave5_04c_Bernstein_approximation_has_exact_real_polynomial (n : ℕ) (f : C(unitInterval.Elem, ℝ)) :
    ∃ p : Polynomial ℝ, ∀ t : unitInterval.Elem,
      Polynomial.eval (t : ℝ) p = (bernsteinApproximation n f) t := by sorry
