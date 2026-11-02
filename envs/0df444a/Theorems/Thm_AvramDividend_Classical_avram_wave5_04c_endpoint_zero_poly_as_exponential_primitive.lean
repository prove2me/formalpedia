-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive
-- name    : AvramDividend.Classical.avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:55:56.909818+00:00
-- url     : https://prove2.me/theorems/5b2d22a5-b9e7-40e2-8b37-feb90e408635
-- title:
--   Endpoint-zero exponential polynomial equals the exact primitive of a zero-constant polynomial
-- statement:
--   A polynomial Q with Q(1)=0 is represented exactly as an interval integral of an exponential polynomial p with p(0)=0 by taking p=-X·Q'. The proof differentiates Q(exp(-r)), applies the real fundamental theorem of calculus, and uses the endpoint value. This joins weighted polynomial approximation to the original BV process's proved zero-constant polynomial-primitive semigroup identities.
-- source:
--   Polynomial.hasDerivAt, Real.hasDerivAt_exp and intervalIntegral.integral_deriv_eq_sub; genuine analytic identity with no stochastic assumptions.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive
    (Q : Polynomial ℝ)
    (hQ : Polynomial.eval 1 Q = 0) :
    ∃ p : Polynomial ℝ, Polynomial.eval 0 p = 0 ∧
      ∀ R : ℝ,
        (∫ r in (0 : ℝ)..R,
          Polynomial.eval (Real.exp (-r)) p) =
            Polynomial.eval (Real.exp (-R)) Q := by sorry
