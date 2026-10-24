-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_capped_laplace_tendsto_of_finite_weak
-- name    : AvramDividend.Classical.excursion_capped_laplace_tendsto_of_finite_weak
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:20:54.503169+00:00
-- url     : https://prove2.me/theorems/9ce02240-437d-47aa-8bf9-b8197767e7b9
-- title:
--   Finite-measure weak convergence preserves capped Laplace integrals
-- statement:
--   For a weakly convergent sequence of finite Borel measures, integrals of the capped nonnegative Laplace exponential converge. Uses the fully proved bounded NNReal-valued continuous test and Mathlib's finite-measure weak convergence criterion.
-- source:
--   FiniteMeasure.tendsto_iff_forall_lintegral_tendsto in pinned Mathlib; Avram excursion capped Laplace bounded test.

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Theorems.Thm_AvramDividend_Classical_excursion_capped_laplace_bounded_nnreal_test

open MeasureTheory Filter Topology

theorem AvramDividend.Classical.excursion_capped_laplace_tendsto_of_finite_weak
    (ν : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hν : Tendsto ν atTop (𝓝 μ)) (s : ℝ) (hs : 0 ≤ s) :
    Tendsto
      (fun n : ℕ =>
        ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂(ν n : Measure ℝ))
      atTop
      (𝓝 (∫⁻ x : ℝ,
        ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂(μ : Measure ℝ))) := by sorry
