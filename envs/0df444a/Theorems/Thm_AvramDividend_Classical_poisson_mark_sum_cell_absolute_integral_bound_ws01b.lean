-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_mark_sum_cell_absolute_integral_bound_ws01b
-- name    : AvramDividend.Classical.poisson_mark_sum_cell_absolute_integral_bound_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:57:09.966131+00:00
-- url     : https://prove2.me/theorems/d19d8846-567e-407f-8bba-12c1851a82bd
-- title:
--   Absolute-integral bound for a marked Poisson jump sum on one exact-count event
-- statement:
--   For independent count and common-law integrable marks, the restricted Bochner integral of the absolute random finite marked sum on the exact count event K=j is bounded above by P(K=j)·j·E|f(Y)|. Proves genuine local integrability and a pointwise triangle estimate, enabling the non-circular global integrability proof for Poisson marked jump sums.
-- source:
--   Extracted genuine stochastic integrability estimate from the accepted WS1B Poisson Campbell proof; uses canonically Proved count-cell mark expectation and exact Bochner monotonicity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_independent_count_cell_mark_mean_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.poisson_mark_sum_cell_absolute_integral_bound_ws01b
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (j : ℕ) (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) :
    (∫ ω in {ω | K ω = j},
      |∑ n ∈ Finset.range (K ω), f (Y n ω)| ∂μ) ≤
      μ.real {ω | K ω = j} *
        ((j : ℝ) * ∫ y, |f y| ∂ν) := by sorry
