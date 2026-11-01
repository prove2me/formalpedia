-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_predictable_marked_grid_bilinear_covariance
-- name    : AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_grid_bilinear_covariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:46:24.99598+00:00
-- url     : https://prove2.me/theorems/fd49fc2f-1fbb-43a3-a222-12cd1806419b
-- title:
--   Stopped finite-grid predictable marked-Poisson bilinear L² covariance
-- statement:
--   For genuine marked Poisson future cells with jointly iid marks and an actual bounded-by-grid stopping index, let three mark profiles F0,F1,F2=F0+F1 satisfy L1∩L2, measurability and filtration-relative independence of each stopped prefix jointly with its current predictable weight from its next future cell. Prove the compensated grid sums S0,S1 have integrable mixed product and derive E[S0*S1]=Σ_i E[Wi²]ri∫F0_i F1_i dν. The proof polarizes three independently proved full-grid L² isometries, establishes S2=S0+S1 on the original probability space, and derives mark inner products by integral linearity. It does not assume any covariance or martingale conclusion.
-- source:
--   P1 canonically Proved stopped marked finite-grid L² isometry UUID 45bd3136-3903-40f7-866d-24438e4eb8bf and pinned Mathlib integral_add, integrable_mul, finite sum algebra.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_predictable_marked_finite_grid_l2_isometry

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_grid_bilinear_covariance
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (r : ℕ → ℝ≥0) (F : Fin 3 → ℕ → E → ℝ)
    (hFadd : ∀ i z, F 2 i z = F 0 i z + F 1 i z)
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
    (hFm : ∀ a i, Measurable (F a i))
    (hFI : ∀ a i, Integrable (F a i) ν)
    (hF2 : ∀ a i, MemLp (F a i) 2 ν)
    (hIncMeas : ∀ a i, Measurable (fun ω =>
      (if i < τ ω then H i ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), F a i (Y i n ω)) -
          (r i : ℝ) * ∫ z, F a i z ∂ν)))
    (hPrefixMeas : ∀ a i, Measurable (fun ω =>
      ∑ j ∈ Finset.range i,
        (if j < τ ω then H j ω else 0) *
          ((∑ n ∈ Finset.range (K j ω), F a j (Y j n ω)) -
            (r j : ℝ) * ∫ z, F a j z ∂ν)))
    (hJointPast : ∀ a i, IndepFun (fun ω =>
      ((∑ j ∈ Finset.range i,
        (if j < τ ω then H j ω else 0) *
          ((∑ n ∈ Finset.range (K j ω), F a j (Y j n ω)) -
            (r j : ℝ) * ∫ z, F a j z ∂ν)),
       if i < τ ω then H i ω else 0))
      (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (m : ℕ) :
    let S : Fin 3 → Ω → ℝ := fun a ω =>
      ∑ i ∈ Finset.range m,
        (if i < τ ω then H i ω else 0) *
          ((∑ n ∈ Finset.range (K i ω), F a i (Y i n ω)) -
            (r i : ℝ) * ∫ z, F a i z ∂ν)
    Integrable (fun ω => S 0 ω * S 1 ω) μ ∧
      (∫ ω, S 0 ω * S 1 ω ∂μ) =
        ∑ i ∈ Finset.range m,
          (∫ ω, (if i < τ ω then H i ω else 0) ^ 2 ∂μ) *
            ((r i : ℝ) * ∫ z, F 0 i z * F 1 i z ∂ν) := by sorry
