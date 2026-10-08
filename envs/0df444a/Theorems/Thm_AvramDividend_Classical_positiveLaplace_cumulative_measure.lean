-- Prove2me | Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
-- name    : AvramDividend.Classical.positiveLaplace_cumulative_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T20:57:31.40066+00:00
-- url     : https://prove2.me/theorems/6027eb2c-dd62-40f1-862a-e614c778e0db
-- title:
--   Laplace transform of a positive cumulative measure on the half-line
-- statement:
--   Let β be an s-finite measure on the real line with no mass below zero, and let s>0. Then the positive Laplace transform on (0,∞) of the cumulative function x↦β((−∞,x]) equals 1/s times the positive Laplace transform of β. The proof writes the cumulative mass as an indicator integral, applies Tonelli to the region 0<x and z≤x, evaluates the resulting exponential tail integral, and uses the support assumption to replace max(0,z) by z almost everywhere.
-- source:
--   Tonelli/Fubini for nonnegative integrands, pinned Mathlib MeasureTheory.lintegral_lintegral_swap, MeasureTheory.lintegral_indicator, Measure.restrict_restrict, Measure.restrict_Ioi_eq_restrict_Ici, measure_eq_zero_iff_ae_notMem, and the standard exponential tail integral. This is the generic Step E identity required to identify the bounded-variation renewal cumulative with the exponentially tilted q-scale function.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace AvramDividend.Classical

/-- For an s-finite measure supported on the nonnegative half-line, the Laplace
transform of its cumulative mass is the measure's Laplace transform divided by s. -/
theorem positiveLaplace_cumulative_measure
    (β : Measure ℝ) [SFinite β] (s : ℝ) (hs : 0 < s)
    (hsupp : β (Iio 0) = 0) :
    (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
      ENNReal.ofReal (1 / s) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂β) := by
  sorry

end AvramDividend.Classical
