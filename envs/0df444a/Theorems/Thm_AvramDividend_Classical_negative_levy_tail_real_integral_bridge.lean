-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_levy_tail_real_integral_bridge
-- name    : AvramDividend.Classical.negative_levy_tail_real_integral_bridge
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:54:07.375337+00:00
-- url     : https://prove2.me/theorems/847641c4-f1d3-4d68-bcc0-00633b25d851
-- title:
--   Finite real compensated-tail integral from Lévy quadratic and large-first-moment conditions
-- statement:
--   For any negative-supported Lévy measure with finite quadratic Lévy moment and finite first moment for large negative marks, the compensated exponential primitive is integrable against the original measure, its original negative-tail density is integrable against Lebesgue measure, and their real integrals coincide. This is the essential finiteness and ENNReal-to-real conversion under unbounded small-jump variation.
-- source:
--   Original negative-mark compensated Tonelli (4cd8a2cf), quadratic bound 1-exp(-θt)≤θt, standing large-mark first moment; target 0fded7ba.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.negative_levy_tail_real_integral_bridge
    (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (hQuad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν ∧
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) (Ioi (0 : ℝ)) ∧
    (∫ y : ℝ, ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t) ∂ν) =
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) := by sorry
