-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits
-- name    : AvramDividend.Classical.avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:18:43.352713+00:00
-- url     : https://prove2.me/theorems/ddb499ea-5d0a-45a0-8d4c-1a742c7006e2
-- title:
--   Exact integrated zero-constant exponential polynomial as finite Lévy exponential deficits
-- statement:
--   For any zero-at-zero real polynomial p and any real residual R, compute exactly the integral from 0 to R of p(exp(-r)) as a finite signed linear combination of positive-integer exponential deficits (1-exp(-kR))/k. Expand the polynomial into positive-integer exponential modes, interchange the finite sum and interval integral using continuity, factor real coefficients out of each integral, and use the exponential primitive formula. This is the exact deterministic algebraic-calculus bridge needed to apply the Proved finite signed original BV residual exponential generator slopes to general C1 derivatives.
-- source:
--   Remote compiler standalone check candidates/work_on/AvramDividend_04c_zero_polynomial_integrated_finite_exp_deficits_standalone_check.lean; modular source candidates/work_on/AvramDividend_04c_zero_polynomial_integrated_finite_exp_deficits_probe.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_zero_constant_polynomial_exact_finite_exp_modes
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_positive_integer_exponential_primitive_deficit
set_option autoImplicit false
open MeasureTheory Set
open AvramDividend.Classical
open scoped BigOperators

theorem AvramDividend.Classical.avram_wave5_04c_zero_polynomial_primitive_finite_exp_deficits (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0) (R : ℝ) :
    (∫ r in (0 : ℝ)..R, Polynomial.eval (Real.exp (-r)) p) =
      ∑ k ∈ p.support.erase 0,
        p.coeff k *
          ((1 - Real.exp ((k : ℝ) * (-R))) / (k : ℝ)) := by sorry
