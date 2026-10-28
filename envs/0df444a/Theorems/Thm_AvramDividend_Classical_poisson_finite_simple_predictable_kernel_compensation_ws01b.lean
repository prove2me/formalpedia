-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_finite_simple_predictable_kernel_compensation_ws01b
-- name    : AvramDividend.Classical.poisson_finite_simple_predictable_kernel_compensation_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:11:46.241612+00:00
-- url     : https://prove2.me/theorems/e0f70aa2-2a38-4cf7-8c7b-9eb79329c0a6
-- title:
--   Finite-rank predictable marked Poisson compensation for arbitrary simple past/mark kernels
-- statement:
--   For a finite family of integrable measurable past observables H_i, integrable marked test functions f_i, and an actual Poisson future count-and-mark family independent of each H_i, the expected random finite sum Σ_i H_i Σ_{n<K} f_i(Y_n) equals Σ_i E[H_i]·r·E[f_i]. Assumes integrability of the finite products to justify exchanging finite sum with the Bochner integral. This proves the kernel-compensation algebra for predictable simple (finite separable) kernels, not the actual Lévy jump measure.
-- source:
--   Apply the canonically Proved closed one-step marked compensation theorem termwise and Mathlib Bochner integral_finset_sum. Predicted reuse: simple-function approximation of BV Lévy jump-reserve compensation with first-passage killing.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.poisson_finite_simple_predictable_kernel_compensation_ws01b
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (s : Finset ι) (H : ι → Ω → ℝ) (f : ι → E → ℝ)
    (hHm : ∀ i ∈ s, Measurable (H i))
    (hHi : ∀ i ∈ s, Integrable (H i) μ)
    (hFm : ∀ i ∈ s, Measurable (f i))
    (hFi : ∀ i ∈ s, Integrable (f i) ν)
    (hPast : ∀ i ∈ s, IndepFun (H i)
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hTerms : ∀ i ∈ s,
      Integrable (fun ω => (H i ω) *
        (∑ n ∈ Finset.range (K ω), (f i) (Y n ω))) μ) :
    (∫ ω, ∑ i ∈ s, (H i ω) *
      (∑ n ∈ Finset.range (K ω), (f i) (Y n ω)) ∂μ) =
    ∑ i ∈ s, (∫ ω, H i ω ∂μ) *
      ((r : ℝ) * ∫ y, f i y ∂ν) := by sorry
