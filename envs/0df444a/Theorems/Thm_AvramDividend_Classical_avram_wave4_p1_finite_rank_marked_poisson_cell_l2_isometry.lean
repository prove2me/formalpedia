-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_rank_marked_poisson_cell_l2_isometry
-- name    : AvramDividend.Classical.avram_wave4_p1_finite_rank_marked_poisson_cell_l2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:16:47.144637+00:00
-- url     : https://prove2.me/theorems/07fdfe52-52f2-47dd-ab66-c65a14a8b26e
-- title:
--   Finite-rank genuinely predictable marked-Poisson cell L² Gram isometry
-- statement:
--   For one genuine original-space marked Poisson count and full iid marks, any finite family of measurable square-integrable past weights H_i and mark profiles f_i in L1∩L2 with each past weight and each sum H_i+H_j independent of the full marked future, prove the finite-rank compensated integral sum is L2 and its exact energy equals the finite Gram quadratic form Σ_{i,j}E[H_i H_j]r∫ f_i(z)f_j(z)ν(dz). Proof uses the independently proved different-past-weight bilinear compensated marked covariance on each tensor pair, finite-sum Bochner integrability, and a double-sum expansion of the square; no covariance, isometry or martingale conclusion is assumed.
-- source:
--   P1 two-past-weight marked one-cell covariance candidate 20056 pending; pinned Mathlib integrable_finset_sum and integral_finset_sum, Finset.sum_mul and Finset.mul_sum.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_two_past_weights_marked_cell_covariance

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave4_p1_finite_rank_marked_poisson_cell_l2_isometry
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (s : Finset ι) (H : ι → Ω → ℝ) (f : ι → E → ℝ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0)
    (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hHm : ∀ i ∈ s, Measurable (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => H i ω ^ 2) μ)
    (hPast : ∀ i ∈ s,
      IndepFun (H i) (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hPastSum : ∀ i ∈ s, ∀ j ∈ s,
      IndepFun (fun ω => H i ω + H j ω)
        (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (hfm : ∀ i ∈ s, Measurable (f i))
    (hfI : ∀ i ∈ s, Integrable (f i) ν)
    (hf2 : ∀ i ∈ s, MemLp (f i) 2 ν) :
    let A : ι → Ω → ℝ := fun i ω =>
      H i ω * ((∑ n ∈ Finset.range (K ω), f i (Y n ω)) -
        (r : ℝ) * ∫ z, f i z ∂ν)
    Integrable (fun ω => (∑ i ∈ s, A i ω) ^ 2) μ ∧
      (∫ ω, (∑ i ∈ s, A i ω) ^ 2 ∂μ) =
        ∑ i ∈ s, ∑ j ∈ s,
          (∫ ω, H i ω * H j ω ∂μ) * (r : ℝ) *
            (∫ z, f i z * f j z ∂ν) := by sorry
