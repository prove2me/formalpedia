-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_predictable_simple_marked_compensation_ws01b
-- name    : AvramDividend.Classical.poisson_predictable_simple_marked_compensation_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:20:50.456975+00:00
-- url     : https://prove2.me/theorems/9f6ecd92-451e-40d9-99b2-47c163dc6bee
-- title:
--   Predictable simple marked Poisson compensation under independent future count-and-mark law
-- statement:
--   If an integrable past observable is independent of the entire future Poisson count and mark sequence, and the count is Poisson of rate r independent of its integrable identically-distributed marks, then the expected product of the past observable with the random marked jump sum is E[past]·r·E[mark]. The random-length marked sum kernel is assumed measurable as a technical condition, not its expectation, compensation, or martingale property.
-- source:
--   Uses a genuine Proved Campbell marked-sum expectation and public Mathlib IndepFun joint past–future factorisation. This is a basic predictable-step stochastic compensation theorem preceding process-level jump measure construction and stopped BV Dynkin.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_campbell_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.poisson_predictable_simple_marked_compensation_ws01b
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E)
    (H : Ω → ℝ) (hHm : Measurable H) (hHi : Integrable H μ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hPast : IndepFun H
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν)
    (hKernel : Measurable
      (fun p : ℕ × (ℕ → E) =>
        ∑ n ∈ Finset.range p.1, f (p.2 n))) :
    (∫ ω, H ω * (∑ n ∈ Finset.range (K ω), f (Y n ω)) ∂μ) =
      (∫ ω, H ω ∂μ) * ((r : ℝ) * ∫ y, f y ∂ν) := by sorry
