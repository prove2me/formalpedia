-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_levy_tail_real_integral_bridge_corrected
-- name    : AvramDividend.Classical.negative_levy_tail_real_integral_bridge_corrected
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:13:49.643672+00:00
-- url     : https://prove2.me/theorems/0793852f-9893-4a01-bd97-9a3dc7e51ea2
-- title:
--   Corrected negative Lévy tail real-integral bridge with the outer Lévy measure
-- statement:
--   For a Lévy measure supported on the negative half-line with finite Lévy quadratic mass and integrable large negative marks, the compensated exponential primitive is integrable against the Lévy measure, the real tail-weighted kernel is integrable on positive times, and Tonelli gives their equality. The measure ν belongs to the outer y-integral. This corrects a prior source statement that accidentally attached ν to the inner time integral.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.negative_levy_tail_real_integral_bridge_corrected
    (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (hQuad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν ∧
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-θ * t)) *
      (ν (Iio (-t))).toReal) (Ioi (0 : ℝ)) ∧
    (∫ y : ℝ, (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ∂ν) =
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) := by sorry
