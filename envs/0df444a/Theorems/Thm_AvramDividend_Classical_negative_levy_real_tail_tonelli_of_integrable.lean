-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_levy_real_tail_tonelli_of_integrable
-- name    : AvramDividend.Classical.negative_levy_real_tail_tonelli_of_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:17:02.945147+00:00
-- url     : https://prove2.me/theorems/59a18d19-52d0-4ac1-84ab-4039c29a8cae
-- title:
--   Real compensated negative-tail Tonelli from finite primitive and finite positive tails
-- statement:
--   From exact original negative-tail nonnegative Tonelli, use primitive integrability and pointwise finite original negative-tail mass to pass ENNReal integral identity to a real Bochner integral with measurability, establishing integrability on (0,∞) and equality. Distinct nontrivial analytic conversion from primitive bounds.
-- source:
--   Original finite-negative-mark Lévy exponent-to-tail identity 0fded7ba-04d9-4ecf-8fe6-044f9c8c72cb, source bridge 847641c4-f1d3-4d68-bcc0-00633b25d851, pinned exact Mathlib revision; Proved 4cd8a2cf original layercake and e44e5f40 compensated primitive bounds.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.negative_levy_real_tail_tonelli_of_integrable
    (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (hTailFin : ∀ t : ℝ, 0 < t → ν (Iio (-t)) < ⊤)
    (θ : ℝ) (hθ : 0 < θ)
    (hFn : Integrable (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν) :
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) (Ioi (0 : ℝ)) ∧
    (∫ y : ℝ, ∫ t in (0 : ℝ)..(-y),
      1 - Real.exp (-θ * t) ∂ν) =
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) := by sorry
