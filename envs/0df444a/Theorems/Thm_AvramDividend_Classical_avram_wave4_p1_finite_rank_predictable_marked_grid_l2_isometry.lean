-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_rank_predictable_marked_grid_l2_isometry
-- name    : AvramDividend.Classical.avram_wave4_p1_finite_rank_predictable_marked_grid_l2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:31:32.050419+00:00
-- url     : https://prove2.me/theorems/40c50cf5-35d6-4372-97db-089e9bb68bac
-- title:
--   Original-space finite-rank predictable marked Poisson grid L² Gram isometry
-- statement:
--   For each cell of a finite deterministic time grid, let the genuinely predictable mark kernel be a finite sum of distinct past-square-integrable random coefficients W_{i,a}(ω) times integrable square-integrable marks f_{i,a}(z). Assume original-space Poisson independent-count iid-mark cells and joint independence of the entire previous compensated prefix together with each next past coefficient from each next cell's full count-and-marks future; each coefficient pair sum is likewise future-independent. Prove integrability of the accumulated squared compensated integral and its exact energy Σ_i Σ_{a,b} E[W_{i,a}W_{i,b}] r_i ∫f_{i,a}f_{i,b}dν. Derive by the finite-rank genuine marked cell Gram theorem, marked future cross orthogonality, square expansion and induction. Any bounded stopping can be included in W, assuming it remains cell-predictable. No isometry, martingale or compensation conclusion is assumed.
-- source:
--   Requires canonically Proved finite-rank one-cell Gram L² theorem (authoring publication pending 02d547f7) and Proved past future marked cross orthogonality d1f079f5, pinned MemLp integrable-square bridge.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_rank_marked_poisson_cell_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_future_cross_orthogonality

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave4_p1_finite_rank_predictable_marked_grid_l2_isometry
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (s : Finset ι) (W : ℕ → ι → Ω → ℝ) (f : ℕ → ι → E → ℝ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E) (r : ℕ → ℝ≥0)
    (hKm : ∀ i, Measurable (K i)) (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) μ)
    (hYm : ∀ i n, Measurable (Y i n)) (hYL : ∀ i n, HasLaw (Y i n) ν μ)
    (hYi : ∀ i, iIndepFun (Y i) μ) (hCountMarks : ∀ i,
      IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) μ)
    (hWm : ∀ i a, a ∈ s → Measurable (W i a)) (hW2 : ∀ i a, a ∈ s → Integrable (fun ω => W i a ω ^ 2) μ)
    (hPast : ∀ i a, a ∈ s →
      IndepFun (W i a) (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (hPastSum : ∀ i a, a ∈ s → ∀ b, b ∈ s →
      IndepFun (fun ω => W i a ω + W i b ω)
        (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (hfm : ∀ i a, a ∈ s → Measurable (f i a)) (hfI : ∀ i a, a ∈ s → Integrable (f i a) ν) (hf2 : ∀ i a, a ∈ s → MemLp (f i a) 2 ν)
    (hPrefixMeas : ∀ i, Measurable (fun ω =>
      ∑ j ∈ Finset.range i, ∑ a ∈ s,
        W j a ω * ((∑ n ∈ Finset.range (K j ω), f j a (Y j n ω)) -
          (r j : ℝ) * ∫ z, f j a z ∂ν)))
    (hJointPast : ∀ i a, a ∈ s →
      IndepFun (fun ω =>
        ((∑ j ∈ Finset.range i, ∑ b ∈ s,
          W j b ω * ((∑ n ∈ Finset.range (K j ω), f j b (Y j n ω)) -
            (r j : ℝ) * ∫ z, f j b z ∂ν)), W i a ω))
      (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (m : ℕ) :
    Integrable (fun ω => (∑ i ∈ Finset.range m, ∑ a ∈ s,
      W i a ω * ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
        (r i : ℝ) * ∫ z, f i a z ∂ν)) ^ 2) μ ∧
    (∫ ω, (∑ i ∈ Finset.range m, ∑ a ∈ s,
      W i a ω * ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
        (r i : ℝ) * ∫ z, f i a z ∂ν)) ^ 2 ∂μ) =
      ∑ i ∈ Finset.range m, ∑ a ∈ s, ∑ b ∈ s,
        (∫ ω, W i a ω * W i b ω ∂μ) * (r i : ℝ) *
          (∫ z, f i a z * f i b z ∂ν) := by sorry
