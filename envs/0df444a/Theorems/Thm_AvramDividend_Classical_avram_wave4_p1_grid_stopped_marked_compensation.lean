-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_grid_stopped_marked_compensation
-- name    : AvramDividend.Classical.avram_wave4_p1_grid_stopped_marked_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:58:25.113344+00:00
-- url     : https://prove2.me/theorems/4df712c4-0cc2-4a12-a742-a42be18ba593
-- title:
--   Finite-grid stopped predictable marked-Poisson compensation with cellwise future independence
-- statement:
--   On a genuine probability space, each deterministic time cell carries a Poisson number of independent-of-count marks with the specified mark distribution. The cell's stopped coefficient (active only before the grid-valued stopping index) is measurable, integrable and independent of its future count-and-mark family. The expectation of the finite sum of stopped marked cell rewards equals the sum of the corresponding intensity integrals, with integrability stated explicitly. No Campbell identity or martingale premise is assumed. The theorem is a finite-grid stopped predictable compensation step; continuum predictable L1 and infinite-activity L2 extension remain separate obligations.
-- source:
--   Proved one-cell marked-Poisson compensation theorem 33961fb8-62cf-4cb9-9a1a-b4a1eef4f1e9, finite Bochner integral linearity. Applebaum, Levy Processes and Stochastic Calculus (2nd ed.), Chapters 2 and 4; Avram–Palmowski–Pistorius (2007), Proposition 4(i).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_grid_stopped_marked_compensation
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (s : Finset ℕ)
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (r : ℕ → ℝ≥0) (f : ℕ → E → ℝ)
    (hKm : ∀ i ∈ s, Measurable (K i))
    (hKlaw : ∀ i ∈ s, HasLaw (K i) (poissonMeasure (r i)) μ)
    (hYm : ∀ i ∈ s, ∀ n, Measurable (Y i n))
    (hYL : ∀ i ∈ s, ∀ n, HasLaw (Y i n) ν μ)
    (hCountMarks : ∀ i ∈ s,
      IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) μ)
    (hWm : ∀ i ∈ s,
      Measurable (fun ω => if i < τ ω then H i ω else 0))
    (hWi : ∀ i ∈ s,
      Integrable (fun ω => if i < τ ω then H i ω else 0) μ)
    (hPast : ∀ i ∈ s,
      IndepFun (fun ω => if i < τ ω then H i ω else 0)
        (fun ω => (K i ω, fun n : ℕ => Y i n ω)) μ)
    (hf : ∀ i ∈ s, Measurable (f i))
    (hfI : ∀ i ∈ s, Integrable (f i) ν)
    (hProdInt : ∀ i ∈ s,
      Integrable (fun ω =>
        (if i < τ ω then H i ω else 0) *
          ∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) μ) :
    (∫ ω, ∑ i ∈ s,
      (if i < τ ω then H i ω else 0) *
        (∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) ∂μ) =
      ∑ i ∈ s, (∫ ω, (if i < τ ω then H i ω else 0) ∂μ) *
        ((r i : ℝ) * ∫ y, f i y ∂ν) := by sorry
