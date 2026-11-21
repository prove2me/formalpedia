-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_levy_compensated_primitive_integrable
-- name    : AvramDividend.Classical.negative_levy_compensated_primitive_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T21:17:03.769177+00:00
-- url     : https://prove2.me/theorems/8ee34d65-68d4-48a4-a7a6-4ed94d3afd25
-- title:
--   Original Lévy compensated primitive is integrable under quadratic and large-first-moment hypotheses
-- statement:
--   Prove integrability of Fθ(-y)=∫₀^{-y}(1-exp(-θt))dt using Fθ(z)≤θz²/2 for small negative marks, Fθ(z)≤z for large marks, quadratic Lévy measure and integrable large marks. Valid with infinite small-jump first variation.
-- source:
--   Original finite-negative-mark Lévy exponent-to-tail identity 0fded7ba-04d9-4ecf-8fe6-044f9c8c72cb, source bridge 847641c4-f1d3-4d68-bcc0-00633b25d851, pinned exact Mathlib revision; Proved 4cd8a2cf original layercake and e44e5f40 compensated primitive bounds.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.negative_levy_compensated_primitive_integrable
    (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (hQuad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν := by sorry
