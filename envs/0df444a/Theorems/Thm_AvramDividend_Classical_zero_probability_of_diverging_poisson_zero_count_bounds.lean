-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_probability_of_diverging_poisson_zero_count_bounds
-- name    : AvramDividend.Classical.zero_probability_of_diverging_poisson_zero_count_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:54:15.643784+00:00
-- url     : https://prove2.me/theorems/938caa2c-169c-461f-8233-92a07c3ef1cb
-- title:
--   Diverging Poisson zero-count intensities force a null event
-- statement:
--   Let A be an event in a probability space. If its probability is bounded above by e^{-λ_n} for every n, with λ_n tending to +∞, then A is null. This is the exact analytic/probabilistic limit step for proving that a Lévy jump process of infinite negative-jump intensity has a jump in every positive initial interval, after the Poisson band-count law has been established.
-- source:
--   Avram, Palmowski and Pistorius (2007), zero-barrier and infinite-jump-activity discussion after equation (3.13), https://arxiv.org/pdf/math/0702893; Mathlib Topology.Order.OrderClosed and Analysis.SpecialFunctions.Exp.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic

open MeasureTheory Set Filter
open scoped ENNReal

namespace AvramDividend.Classical

/-- A probability event bounded by the zero-count tails of diverging Poisson intensities is null. -/
theorem zero_probability_of_diverging_poisson_zero_count_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (rates : ℕ → ℝ)
    (hrates : Tendsto rates atTop atTop)
    (hbound : ∀ n : ℕ, (P A).toReal ≤ Real.exp (-(rates n))) :
    P A = 0 := by sorry

end AvramDividend.Classical
