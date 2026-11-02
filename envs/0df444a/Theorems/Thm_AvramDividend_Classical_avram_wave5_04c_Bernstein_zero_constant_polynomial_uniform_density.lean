-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_zero_constant_polynomial_uniform_density
-- name    : AvramDividend.Classical.avram_wave5_04c_Bernstein_zero_constant_polynomial_uniform_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:51:50.089598+00:00
-- url     : https://prove2.me/theorems/a95e5956-46a5-48af-8291-4ecc04368bb1
-- title:
--   Uniform Bernstein approximation by a real polynomial vanishing at zero
-- statement:
--   Uniformly approximate any continuous real-valued function on the unit interval vanishing at zero by a real polynomial also vanishing exactly at zero. Select a sufficiently large Bernstein approximation using Mathlib uniform convergence, extract its exact polynomial representation, and preserve the endpoint value by bernsteinApproximation.apply_zero. Explicit uniform absolute error below any ε>0 holds throughout the unit interval, including zero. This is a quantitative algebraic approximation helper for the original Lévy BV C1 generator-semigroup bridge.
-- source:
--   Verified standalone remote compiler with explicit Bernstein polynomial construction candidates/work_on/AvramDividend_04c_Bernstein_zero_constant_density_standalone_check.lean; dependent proof candidates/work_on/AvramDividend_04c_Bernstein_zero_constant_polynomial_density_probe.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_approximation_has_exact_real_polynomial
set_option autoImplicit false
open Filter Set
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_Bernstein_zero_constant_polynomial_uniform_density (f : C(unitInterval.Elem, ℝ)) (h0 : f 0 = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, Polynomial.eval 0 p = 0 ∧
      ∀ t : unitInterval.Elem,
        |Polynomial.eval (t : ℝ) p - f t| < ε := by sorry
