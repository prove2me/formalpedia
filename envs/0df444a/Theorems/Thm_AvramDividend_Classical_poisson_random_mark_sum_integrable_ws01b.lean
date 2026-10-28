-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_integrable_ws01b
-- name    : AvramDividend.Classical.poisson_random_mark_sum_integrable_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:08:07.316213+00:00
-- url     : https://prove2.me/theorems/73e77c39-1837-472f-aad7-4098f3748a34
-- title:
--   Random Poisson-count marked sum is Bochner integrable under the exact mark first moment
-- statement:
--   For a Poisson-law random count and identically-law integrable marks independent of that count, the random-length sum of the marks' measurable test function is genuinely Bochner integrable, including unbounded but L1 marks. Uses a disjoint exact-count partition, absolute restricted integral estimates, summability of the Poisson first moment, and a valid integrable-on-union theorem; no assumption of global random-sum integrability.
-- source:
--   Extracted from the accepted genuine WS1B Campbell proof and the separately proved count-cell absolute norm inequality, exposing the exact L1 fact needed to remove product-integrability hypotheses from predictable finite-rank compensation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_mark_sum_cell_absolute_integral_bound_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.poisson_random_mark_sum_integrable_ws01b
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν) :
    Integrable (fun ω => ∑ n ∈ Finset.range (K ω), f (Y n ω)) μ := by sorry
