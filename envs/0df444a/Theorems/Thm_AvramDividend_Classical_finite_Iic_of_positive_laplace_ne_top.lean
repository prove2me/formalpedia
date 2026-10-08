-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_Iic_of_positive_laplace_ne_top
-- name    : AvramDividend.Classical.finite_Iic_of_positive_laplace_ne_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T20:21:34.14042+00:00
-- url     : https://prove2.me/theorems/27cceb38-1184-4273-b283-6e5e25d9f024
-- title:
--   Finite positive Laplace mass gives finite lower cumulative mass
-- statement:
--   Let β be a measure on the real line and let s>0. If the positive Laplace integral ∫ exp(-s z) dβ(z) is finite, then β((-∞,x]) is finite for every real x. This follows from the lower bound exp(-s z) ≥ exp(-s x) on z≤x and Markov's inequality.
-- source:
--   Pinned Mathlib MeasureTheory.Integral.Lebesgue.Markov theorem meas_ge_le_lintegral_div, together with monotonicity of Real.exp and ENNReal.ofReal. This generic measure lemma supplies the local-finiteness hypothesis needed by the bounded-variation renewal representation for AvramDividend.Classical.scaleFunction_tilted_positive_monotone_of_bv.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

namespace AvramDividend.Classical

/-- A finite positive Laplace transform at one positive parameter forces
all lower cumulative intervals to have finite measure. -/
theorem finite_Iic_of_positive_laplace_ne_top
    (β : Measure ℝ) (s x : ℝ) (hs : 0 < s)
    (hLap :
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂β) ≠ ∞) :
    β (Iic x) ≠ ∞ := by
  sorry

end AvramDividend.Classical
