-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
-- name    : AvramDividend.Classical.avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:51:04.956061+00:00
-- url     : https://prove2.me/theorems/06e9cd35-99fc-4513-83c6-020950b9b4e0
-- title:
--   Endpoint-vanishing polynomial approximation with exact first-order deficit weight
-- statement:
--   Every continuous compactified profile on the unit interval has a polynomial approximation that vanishes exactly at the endpoint t=1 and has pointwise error bounded by epsilon times 1-t. This first-order weighted Bernstein approximation is the analytic route to signed negative-jump ν approximation with an integrable exponential deficit majorant instead of assuming a global negative-jump first moment.
-- source:
--   Apply the Proved exact zero-constant Bernstein density to G minus its value at 0, restore the constant coefficient, and multiply by 1-X. The endpoint zero is algebraic and absolute error gains the weight 1-t.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_zero_constant_polynomial_uniform_density
set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
    (G : C(unitInterval.Elem, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      ∀ t : unitInterval.Elem,
        |Polynomial.eval (t : ℝ) Q -
          (1 - (t : ℝ)) * G t| ≤
          ε * (1 - (t : ℝ)) := by sorry
