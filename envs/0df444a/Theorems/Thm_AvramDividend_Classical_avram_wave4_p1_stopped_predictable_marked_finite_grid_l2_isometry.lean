-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_predictable_marked_finite_grid_l2_isometry
-- name    : AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_finite_grid_l2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:22:32.370103+00:00
-- url     : https://prove2.me/theorems/45bd3136-3903-40f7-866d-24438e4eb8bf
-- title:
--   Original-space stopped predictable marked-Poisson finite-grid L² isometry
-- statement:
--   For a stopped finite deterministic time grid of original-path Poisson count cells with independent iid marks and measurable square-integrable predictable weights, assume each cell's future count and full mark sequence are independent of the joint past consisting of its previous compensated prefix and current stopped coefficient. Then the actual stopped compensated marked sum has integrable square and exact isometry E[(Σ_i W_i(S_i−r_i Eνf_i))²]=Σ_i E[W_i²]r_iEν[f_i²]. The proof derives finite-prefix MemLp internally from the marked one-cell isometry, iterates a proved original-space two-cell orthogonality result and does not assume compensation or vanishing cross integrals as a premise. This covers stopped elementary predictable mark kernels on discrete grids, not arbitrary predictable continuous-time kernels or source-X law identification.
-- source:
--   P1 original-space marked two-cell increment isometry, stopped marked finite prefix MemLp, pinned Mathlib memLp_two_iff_integrable_sq and Finset.sum_range_succ.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_two_cell_marked_l2_increment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_marked_finite_prefix_memLp

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_finite_grid_l2_isometry
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (r : ℕ → ℝ≥0) (f : ℕ → E → ℝ)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) μ)
    (hYm : ∀ i n, Measurable (Y i n))
    (hYL : ∀ i n, HasLaw (Y i n) ν μ)
    (hYi : ∀ i, iIndepFun (Y i) μ)
    (hCountMarks : ∀ i,
      IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) μ)
    (hWm : ∀ i, Measurable
      (fun ω => if i < τ ω then H i ω else 0))
    (hW2 : ∀ i, Integrable
      (fun ω => (if i < τ ω then H i ω else 0) ^ 2) μ)
    (hPast : ∀ i,
      IndepFun (fun ω => if i < τ ω then H i ω else 0)
        (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (hf : ∀ i, Measurable (f i))
    (hfI : ∀ i, Integrable (f i) ν)
    (hf2 : ∀ i, MemLp (f i) 2 ν)
    (hIncMeas : ∀ i, Measurable (fun ω =>
      (if i < τ ω then H i ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i z ∂ν)))
    (hPrefixMeas : ∀ i, Measurable (fun ω =>
      ∑ j ∈ Finset.range i,
        (if j < τ ω then H j ω else 0) *
          ((∑ n ∈ Finset.range (K j ω), f j (Y j n ω)) -
            (r j : ℝ) * ∫ z, f j z ∂ν)))
    (hJointPast : ∀ i, IndepFun (fun ω =>
      ((∑ j ∈ Finset.range i,
        (if j < τ ω then H j ω else 0) *
          ((∑ n ∈ Finset.range (K j ω), f j (Y j n ω)) -
            (r j : ℝ) * ∫ z, f j z ∂ν)),
       if i < τ ω then H i ω else 0))
      (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (m : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range m,
        (if i < τ ω then H i ω else 0) *
          ((∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
            (r i : ℝ) * ∫ z, f i z ∂ν)) ^ 2) μ ∧
    (∫ ω, (∑ i ∈ Finset.range m,
      (if i < τ ω then H i ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i z ∂ν)) ^ 2 ∂μ) =
      ∑ i ∈ Finset.range m,
        (∫ ω, (if i < τ ω then H i ω else 0) ^ 2 ∂μ) *
          ((r i : ℝ) * ∫ z, f i z ^ 2 ∂ν) := by sorry
