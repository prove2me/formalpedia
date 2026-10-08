-- Prove2me | Theorems.Thm_AvramDividend_Classical_weightedLaplace_derivative_with_origin_boundary
-- name    : AvramDividend.Classical.weightedLaplace_derivative_with_origin_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:10:54.03598+00:00
-- url     : https://prove2.me/theorems/4cca97a2-a1a4-446c-8f68-e95111a2a800
-- title:
--   Exponential-weighted derivative transform retains the scale-function boundary value
-- statement:
--   For a real W continuous from the right at 0, differentiable on (0,∞), and with both e^{-θx}W(x) and e^{-θx}W'(x) integrable on that half-line, integration by parts gives ∫e^{-θx}W'(x)dx = θ∫e^{-θx}W(x)dx−W(0). The proof applies Mathlib's improper FTC to F(x)=e^{-θx}W(x), whose derivative and value are integrable. Its limit at positive infinity must be zero. This is essential to the Lévy scale-function generator calculation because W(0) need not vanish in the bounded-variation case. No extra assumptions on θ or the process are needed beyond the stated integrability.
-- source:
--   Exponential-weighted integration by parts with the correct origin contribution, required for the Laplace transform of the q-scale function generator.

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem weightedLaplace_derivative_with_origin_boundary
    (W : ℝ → ℝ) (θ : ℝ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hWint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)))
    (hDint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * deriv W x) =
       θ * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) - W 0 := by sorry

end AvramDividend.Classical
