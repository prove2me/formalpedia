-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_marked_finite_prefix_memLp
-- name    : AvramDividend.Classical.avram_wave4_p1_stopped_marked_finite_prefix_memLp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:12:58.871653+00:00
-- url     : https://prove2.me/theorems/13c9cd6c-570e-4ee4-915f-0562ff90386d
-- title:
--   Finite stopped marked-Poisson predictable prefixes are square integrable
-- statement:
--   For all cells of a deterministic time grid, assume a genuine original-space marked Poisson count with independent iid marks, a measurable square-integrable stopped predictable weight independent of its cell future, and measurable L1∩L2 mark kernel. If the actual compensated stopped increment is measurable (as established by controlled-kernel predictability), prove from each one-cell L2 isometry that every finite prefix of the sum of the actual stopped compensated increments belongs to L². This does not assume any finite-prefix L² conclusion or cross-cell orthogonality; it is the independent integrability prerequisite for a marked finite-grid martingale isometry.
-- source:
--   P1 accepted marked past-weighted one-cell L² isometry; pinned Mathlib memLp_two_iff_integrable_sq and MemLp.add; P1 accepted unmarked prefix proof pattern.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave4_p1_stopped_marked_finite_prefix_memLp
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
          (r i : ℝ) * ∫ z, f i z ∂ν))) :
    ∀ m, MemLp (fun ω => ∑ i ∈ Finset.range m,
      (if i < τ ω then H i ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i z ∂ν)) 2 μ := by sorry
