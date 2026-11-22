-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_levy_real_tail_tonelli_outer_measure
-- name    : AvramDividend.Classical.negative_levy_real_tail_tonelli_outer_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T07:55:26.23467+00:00
-- url     : https://prove2.me/theorems/ca910b4f-70c4-417e-9835-35c79caad161
-- title:
--   Finite real negative Lévy-tail Tonelli with explicit outer-jump-measure binding
-- statement:
--   For a negative-supported Lévy mark measure ν with finite negative tails and an integrable compensated primitive, its outer ν-integral of the primitive equals the Lebesgue integral of the compensated original negative-tail kernel, which is integrable. The formula explicitly parenthesises the inner interval integral to ensure the final ∂ν applies to the OUTER Lévy mark integral. This is the actual real-valued Tonelli companion of the already Proved ENNReal source, valid with infinite small-jump first variation.
-- source:
--   Proved original_negative_levy_tail_tonelli 4cd8a2cf, compensated_primitive_bounds e44e5f40, negative_levy_tail_real_conversion_of_finite_lintegral d7387618, generic nonnegative integral conversion 725d1c1a.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.negative_levy_real_tail_tonelli_outer_measure
    (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (hTailFin : ∀ t : ℝ, 0 < t → ν (Iio (-t)) < ⊤)
    (θ : ℝ) (hθ : 0 < θ)
    (hFn : Integrable (fun y : ℝ =>
      ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν) :
    IntegrableOn (fun t : ℝ =>
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal)
      (Ioi (0 : ℝ)) ∧
    (∫ y : ℝ, (∫ t in (0 : ℝ)..(-y),
      1 - Real.exp (-θ * t)) ∂ν) =
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) := by sorry
