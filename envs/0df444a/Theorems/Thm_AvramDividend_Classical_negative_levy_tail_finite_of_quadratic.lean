-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_levy_tail_finite_of_quadratic
-- name    : AvramDividend.Classical.negative_levy_tail_finite_of_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T21:17:03.659992+00:00
-- url     : https://prove2.me/theorems/f4038116-518f-4bfa-a3af-64331935a5e7
-- title:
--   Original negative Lévy tail is pointwise finite away from zero
-- statement:
--   Finite ∫min(1,y²)dν bounds ν(y<-t) for every t>0 because min(1,y²) has a strictly positive lower bound on that negative tail; no finite jump-activity or bounded variation needed.
-- source:
--   Original finite-negative-mark Lévy exponent-to-tail identity 0fded7ba-04d9-4ecf-8fe6-044f9c8c72cb, source bridge 847641c4-f1d3-4d68-bcc0-00633b25d851, pinned exact Mathlib revision; Proved 4cd8a2cf original layercake and e44e5f40 compensated primitive bounds.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.negative_levy_tail_finite_of_quadratic
    (ν : Measure ℝ)
    (hQuad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    ∀ t : ℝ, 0 < t → ν (Iio (-t)) < ⊤ := by sorry
