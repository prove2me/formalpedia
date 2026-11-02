-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_zero_constant_polynomial_exact_finite_exp_modes
-- name    : AvramDividend.Classical.avram_wave5_04c_zero_constant_polynomial_exact_finite_exp_modes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:06:58.59669+00:00
-- url     : https://prove2.me/theorems/2ff09ced-0c32-45a4-bf29-eae55f6ba7b6
-- title:
--   Exact positive-integer exponential-mode expansion of a polynomial vanishing at zero
-- statement:
--   Any real polynomial with evaluation zero at the origin, evaluated at exp(-r), equals exactly the finite signed sum over nonzero coefficient support of p.coeff(k) exp(-k r). Exclude the degree-zero mode by subtracting p(0), using the polynomial finite-support evaluation sum, and erasing the zero index since every term of the difference vanishes there. The strictly positive integer modes are the precise exponential test family for which the original bounded-variation Lévy residual right derivative is already Proved.
-- source:
--   Remote private compiler source candidates/work_on/AvramDividend_04c_zero_constant_polynomial_finite_exp_basis_probe.lean

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem AvramDividend.Classical.avram_wave5_04c_zero_constant_polynomial_exact_finite_exp_modes (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) (r : ℝ) :
    Polynomial.eval (Real.exp (-r)) p =
      ∑ k ∈ p.support.erase 0,
        p.coeff k * Real.exp ((k : ℝ) * (-r)) := by sorry
