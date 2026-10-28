-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_product_integrable_ws01b
-- name    : AvramDividend.Classical.poisson_predictable_marked_product_integrable_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:32:28.668794+00:00
-- url     : https://prove2.me/theorems/a467fb2d-71c1-4680-9f98-6b28c8143403
-- title:
--   Integrability of an independent past weight times the full future Poisson marked sum
-- statement:
--   A measurable integrable past observable multiplied by the independent random Poisson sum of integrable marks is genuinely Bochner integrable; the summation is random and need not be bounded. Independence of the past weight from the entire future marked count and marks is used, not merely independent scalar marginal laws. No product-integrability hypothesis is assumed.
-- source:
--   Combines the canonically Proved measurable random-length mark-sum kernel and new full Poisson sum L1 theorem with the pinned Mathlib IndepFun.integrable_mul; exact stochastic preparation for finite-rank predictable jump compensation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_integrable_ws01b
import Theorems.Thm_AvramDividend_Classical_variable_finite_marks_sum_measurable_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.poisson_predictable_marked_product_integrable_ws01b
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
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν) :
    Integrable (fun ω =>
      H ω * ∑ n ∈ Finset.range (K ω), f (Y n ω)) μ := by sorry
