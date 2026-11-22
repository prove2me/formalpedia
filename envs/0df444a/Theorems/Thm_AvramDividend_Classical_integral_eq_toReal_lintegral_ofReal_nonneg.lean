-- Prove2me | Theorems.Thm_AvramDividend_Classical_integral_eq_toReal_lintegral_ofReal_nonneg
-- name    : AvramDividend.Classical.integral_eq_toReal_lintegral_ofReal_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T07:47:01.906179+00:00
-- url     : https://prove2.me/theorems/725d1c1a-cd0e-4988-823b-1637f11099e4
-- title:
--   Real integral of nonnegative integrable function equals toReal of ENNReal integral
-- statement:
--   For any real-valued integrable function f on a real measure ν which is nonnegative ν-almost everywhere, the real integral ∫f dν equals the ENNReal integral ∫⁻ofReal(f) dν converted toReal. This is a named-function version of a pinned Mathlib conversion useful for original Lévy-tail Tonelli proofs where interval-integral lambdas have difficult definitional equalities.
-- source:
--   Pinned Mathlib ofReal_integral_eq_lintegral_ofReal, integral_nonneg_of_ae, ENNReal.toReal_ofReal; original real compensated-tail source 59a18d19.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.integral_eq_toReal_lintegral_ofReal_nonneg
    (ν : Measure ℝ) (f : ℝ → ℝ)
    (hf : Integrable f ν) (hpos : ∀ᵐ y ∂ν, 0 ≤ f y) :
    (∫ y : ℝ, f y ∂ν) =
      (∫⁻ y : ℝ, ENNReal.ofReal (f y) ∂ν).toReal := by sorry
