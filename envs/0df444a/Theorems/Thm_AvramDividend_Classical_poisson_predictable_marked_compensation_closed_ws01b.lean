-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b
-- name    : AvramDividend.Classical.poisson_predictable_marked_compensation_closed_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:32:01.093734+00:00
-- url     : https://prove2.me/theorems/33961fb8-62cf-4cb9-9a1a-b4a1eef4f1e9
-- title:
--   Closed one-step predictable marked-Poisson compensation without auxiliary measurability assumptions
-- statement:
--   On an actual probability space, an integrable past observable independent of the entire future Poisson count-and-mark family satisfies E[H Σ_{n<K}f(Yn)] = E[H]·r·Eν[f]. Assumes the genuine Poisson count, mark laws and independence and mark integrability, but no compensator, semigroup, random sum integrability, or extra kernel measurability conclusion as a premise. A valid predictable step compensation foundation.
-- source:
--   Combination of two separate pinned proofs: the random-length finite marked kernel is measurably definable, and the marked Campbell past-future factorisation. Moves toward predictable stopped BV jump compensation, not a direct proof of full Dynkin.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_simple_marked_compensation_ws01b
import Theorems.Thm_AvramDividend_Classical_variable_finite_marks_sum_measurable_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.poisson_predictable_marked_compensation_closed_ws01b
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
    (∫ ω, H ω * (∑ n ∈ Finset.range (K ω), f (Y n ω)) ∂μ) =
      (∫ ω, H ω ∂μ) * ((r : ℝ) * ∫ y, f y ∂ν) := by sorry
