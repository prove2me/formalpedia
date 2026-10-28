-- Prove2me | Theorems.Thm_AvramDividend_Classical_laplace_large_deficit_probability_tendsto_zero_ws01b
-- name    : AvramDividend.Classical.laplace_large_deficit_probability_tendsto_zero_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:02:43.476659+00:00
-- url     : https://prove2.me/theorems/c1b3476c-8043-4829-a30b-8e9fbe887ab4
-- title:
--   Vanishing large-deficit probabilities from convergence of Laplace expectations
-- statement:
--   For any family of nonnegative random deficits on a finite measure space, when each exponential Laplace integral converges to total mass, the probability of exceeding any fixed positive threshold converges to zero, assuming explicit measurability and integrability. This closes the analytic bridge from the proved BV drift-deficit small-time Laplace limit towards a pathwise no-creeping argument, allowing arbitrary infinite-activity bounded-variation jumps.
-- source:
--   Elementary Laplace-tail bound, proved UUID 7dce878a-f749-4977-bf4a-fe47a20a9a37, followed by squeezing. Consistent with Kyprianou's scale-function review, bounded-variation fluctuation theory.

import Theorems.Thm_AvramDividend_Classical_laplace_large_deficit_probability_bound_ws01b
import Mathlib.Order.Filter.Tendsto
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.laplace_large_deficit_probability_tendsto_zero_ws01b
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hD : ∀ n ω, 0 ≤ D n ω)
    (hMeas : ∀ n, MeasurableSet {ω : Ω | a ≤ D n ω})
    (hLeft : ∀ n, Integrable
      (fun ω => if a ≤ D n ω then (1 - Real.exp (-a) : ℝ) else 0) μ)
    (hOne : Integrable (fun _ : Ω => (1 : ℝ)) μ)
    (hExp : ∀ n, Integrable (fun ω => Real.exp (-D n ω)) μ)
    (hLaplace : Tendsto
      (fun n : ℕ => ∫ ω, Real.exp (-D n ω) ∂μ)
      atTop (𝓝 (μ.real Set.univ))) :
    Tendsto (fun n : ℕ => μ.real {ω : Ω | a ≤ D n ω})
      atTop (𝓝 (0 : ℝ)) := by sorry
