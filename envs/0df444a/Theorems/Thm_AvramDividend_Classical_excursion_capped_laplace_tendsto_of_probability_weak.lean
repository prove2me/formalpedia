-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_capped_laplace_tendsto_of_probability_weak
-- name    : AvramDividend.Classical.excursion_capped_laplace_tendsto_of_probability_weak
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:05:39.94917+00:00
-- url     : https://prove2.me/theorems/e655827c-5408-44d8-a8c6-183147a76dbc
-- title:
--   Weak convergence preserves capped exponential Laplace integrals
-- statement:
--   If probability measures converge weakly, then the extended nonnegative integrals of the bounded capped Laplace exponential converge to the integral against the limiting probability measure. The supplied previously proved BoundedContinuousFunction test and Mathlib's weak-convergence criterion give the result.
-- source:
--   Prokhorov compactness and Laplace-transform weak limit interface for Avram classical dividend mission.

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Basic

open MeasureTheory Filter Topology

theorem AvramDividend.Classical.excursion_capped_laplace_tendsto_of_probability_weak
    (P : ℕ → ProbabilityMeasure ℝ) (Q : ProbabilityMeasure ℝ)
    (hP : Tendsto P atTop (𝓝 Q)) (s : ℝ) (hs : 0 ≤ s) :
    Tendsto
      (fun n : ℕ =>
        ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂(P n : Measure ℝ))
      atTop
      (𝓝 (∫⁻ x : ℝ,
        ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂(Q : Measure ℝ))) := by sorry
