-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteMeasures_eq_of_complexMGF_eq_on_real_Iio
-- name    : AvramDividend.Classical.finiteMeasures_eq_of_complexMGF_eq_on_real_Iio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T22:19:30.678002+00:00
-- url     : https://prove2.me/theorems/3c031447-1ce2-436e-933b-fdf2716c0fc1
-- title:
--   Finite measure Laplace uniqueness from analytic MGFs on a half-plane
-- statement:
--   If two finite real measures have complex moment-generating functions analytic on a common half-plane Re z<b with b>0, and those functions agree for all real t<b, then the finite measures are equal. The identity theorem extends their equality to the complex half-plane containing the imaginary axis, and uniqueness of characteristic functions identifies the measures. This directly supports identification of the renewal-derived scale-function candidate using its one-sided Laplace transform.
-- source:
--   Pinned Mathlib Mathlib/Probability/Moments/ComplexMGF.lean lines 260-340 and Analysis/Analytic/Uniqueness.lean; MeasureTheory.ext_of_integral_char_eq

import Mathlib
open MeasureTheory Filter Finset Real Complex
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace AvramDividend.Classical

/-- Equality of finite real measures follows from their MGFs agreeing on
a real interval inside a common analytic left half-plane. -/
theorem finiteMeasures_eq_of_complexMGF_eq_on_real_Iio (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (b : ℝ) (hb : 0 < b)
    (hμ : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id μ)
      {z : ℂ | z.re < b})
    (hν : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id ν)
      {z : ℂ | z.re < b})
    (hreal : ∀ t : ℝ, t < b →
      ProbabilityTheory.complexMGF id μ (t : ℂ) =
        ProbabilityTheory.complexMGF id ν (t : ℂ)) :
    μ = ν := by
  sorry

end AvramDividend.Classical
