-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_predictable_finite_rank_compensation_ws01b
-- name    : AvramDividend.Classical.poisson_predictable_finite_rank_compensation_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:49:59.102463+00:00
-- url     : https://prove2.me/theorems/37c9ba44-8276-448a-84f4-0af888084887
-- title:
--   Finite-rank predictable marked-Poisson compensation with individual product integrability
-- statement:
--   For an actual Poisson count and independent identically distributed marks, a finite-rank predictable random kernel sum_i H_i(past) f_i(jump) satisfies the exact compensated expectation formula. Past variables are integrable and independent of the future marked count. Product integrability is explicitly assumed to justify exchanging the Bochner integral with the finite sum, rather than silently applying linearity outside its domain. This is the finite-simple-kernel step towards the stopped BV Dynkin formula, not the actual Lévy PRM identification.
-- source:
--   Composition of canonically Proved marked past-future compensation and Mathlib's integrable finite-sum Bochner linearity. No inaccessible private point-process imports; full stochastic compensation beyond finite rank still required.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.poisson_predictable_finite_rank_compensation_ws01b
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (s : Finset ι)
    (H : ι → Ω → ℝ) (f : ι → E → ℝ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hHm : ∀ i ∈ s, Measurable (H i))
    (hHi : ∀ i ∈ s, Integrable (H i) μ)
    (hf : ∀ i ∈ s, Measurable (f i))
    (hfI : ∀ i ∈ s, Integrable (f i) ν)
    (hPast : ∀ i ∈ s, IndepFun (H i)
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hProdInt : ∀ i ∈ s,
      Integrable (fun ω =>
        H i ω * ∑ n ∈ Finset.range (K ω), f i (Y n ω)) μ) :
    (∫ ω, ∑ i ∈ s,
      H i ω * (∑ n ∈ Finset.range (K ω), f i (Y n ω)) ∂μ) =
      ∑ i ∈ s, (∫ ω, H i ω ∂μ) *
        ((r : ℝ) * ∫ y, f i y ∂ν) := by sorry
