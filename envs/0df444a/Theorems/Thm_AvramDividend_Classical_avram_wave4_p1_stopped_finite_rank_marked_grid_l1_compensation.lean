-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_finite_rank_marked_grid_l1_compensation
-- name    : AvramDividend.Classical.avram_wave4_p1_stopped_finite_rank_marked_grid_l1_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:26:33.636629+00:00
-- url     : https://prove2.me/theorems/429c97c7-32db-4369-aa2f-2badbd98d592
-- title:
--   Stopped finite-grid predictable finite-rank marked Poisson L¹ compensation
-- statement:
--   For a finite time grid of genuine original-space independent-future marked Poisson cells and any finite rank of distinct stopped predictable past coefficients per time cell, with each stopped coefficient in L1 and independent of its future full marked count/marks, and each mark profile in L1(ν), prove actual integrability and mean zero of the full doubly indexed centred stopped marked sum. The finite cell rank may change through mark profiles and past weights over time; stopping is represented directly by if i<τ(ω) then H_i,a else zero and must have the specified past/future measurability and independence. Derive by the now-canonical Proved finite-rank one-cell L1 Campbell and finite-grid integration linearity; no martingale mean-zero premise.
-- source:
--   Canonical Proved finite-rank original-space marked-cell L1 compensation bbd1e1c5-f3ca-4cd7-9a7d-7e2c5cea2e2c, candidate 20078 ACCEPTED. Pinned integral_finset_sum and integrable_finset_sum.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_rank_marked_cell_l1_compensation

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave4_p1_stopped_finite_rank_marked_grid_l1_compensation
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E)
    (s : Finset ι) (m : ℕ)
    (H : ℕ → ι → Ω → ℝ) (τ : Ω → ℕ) (f : ℕ → ι → E → ℝ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E) (r : ℕ → ℝ≥0)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) μ)
    (hYm : ∀ i n, Measurable (Y i n))
    (hYL : ∀ i n, HasLaw (Y i n) ν μ)
    (hCountMarks : ∀ i,
      IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) μ)
    (hWm : ∀ i a, a ∈ s →
      Measurable (fun ω => if i < τ ω then H i a ω else 0))
    (hWi : ∀ i a, a ∈ s →
      Integrable (fun ω => if i < τ ω then H i a ω else 0) μ)
    (hPast : ∀ i a, a ∈ s →
      IndepFun (fun ω => if i < τ ω then H i a ω else 0)
        (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (hfm : ∀ i a, a ∈ s → Measurable (f i a))
    (hfI : ∀ i a, a ∈ s → Integrable (f i a) ν) :
    Integrable (fun ω => ∑ i ∈ Finset.range m, ∑ a ∈ s,
      (if i < τ ω then H i a ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i a z ∂ν)) μ ∧
    (∫ ω, ∑ i ∈ Finset.range m, ∑ a ∈ s,
      (if i < τ ω then H i a ω else 0) *
        ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i a z ∂ν) ∂μ) = 0 := by sorry
