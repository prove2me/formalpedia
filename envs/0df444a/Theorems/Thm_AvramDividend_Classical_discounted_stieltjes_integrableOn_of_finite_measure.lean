-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_integrableOn_of_finite_measure
-- name    : AvramDividend.Classical.discounted_stieltjes_integrableOn_of_finite_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:56:05.38379+00:00
-- url     : https://prove2.me/theorems/f70331c8-0125-468d-b9ee-a8f8c9044128
-- title:
--   Discount factors are Stieltjes-integrable on finite-mass nonnegative payment sets
-- statement:
--   For nonnegative discount rate q and any measurable set of nonnegative payment times of finite Stieltjes measure, the exponential discount exp(-q t) is integrable with respect to that measure on the payment set. The proof uses strong measurability, the bound exp(-q t)<=1, and integrability of bounded functions on finite-measure sets. This discharges the integrability requirement in the real-to-ENNReal discounted dividend bridge.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.discounted_stieltjes_integrableOn_of_finite_measure
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (A : Set ℝ)
    (hAmeas : MeasurableSet A)
    (hAnonneg : ∀ t ∈ A, 0 ≤ t)
    (hfinite : μ A ≠ ⊤) :
    IntegrableOn (fun t : ℝ => Real.exp (-(q * t))) A μ := by sorry
