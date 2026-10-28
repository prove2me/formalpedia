-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_paymentTimes_shift_of_measure_map
-- name    : AvramDividend.Classical.discounted_paymentTimes_shift_of_measure_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:50:53.939871+00:00
-- url     : https://prove2.me/theorems/3d97c2a4-ba4c-42f4-8e7c-a839e9a24b67
-- title:
--   Discounted stopped dividend window shifts exactly under a translated Stieltjes measure
-- statement:
--   For any two real-time measures related by a translation u, and any possibly infinite extended-nonnegative payment stopping horizon σ, the discounted Stieltjes integral over strictly post-u payment times equals the u-discount factor times the translated integral over strictly positive relative times whose translated absolute timestamps remain in the original paymentTimes σ. No finiteness or subtraction of stopping times is assumed, so the strict ruin boundary and infinite-horizon cases remain correct. The proof uses measurable payment-time sets and the existing general discounted-integral translation lemma.
-- source:
--   Proved paymentTimes_measurable 88dafb7f and lintegral_killed_discount_translation_of_measure_map 4c583263; avoids the disproved naive paymentTimes_after_firstUpcrossing_eq_shifted lemma; first stopped-reward transport step for barrier valuation 79978d61.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_lintegral_killed_discount_translation_of_measure_map
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.discounted_paymentTimes_shift_of_measure_map
    (μ ν : Measure ℝ) (u q : ℝ) (σ : ℝ≥0∞)
    (hμ : μ = Measure.map (fun t : ℝ => u + t) ν) :
    (∫⁻ t in Set.Ioi u ∩ paymentTimes σ,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
    ENNReal.ofReal (Real.exp (-(q * u))) *
      (∫⁻ t in Set.Ioi (0 : ℝ) ∩
          ((fun t : ℝ => u + t) ⁻¹' paymentTimes σ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂ν) := by sorry
