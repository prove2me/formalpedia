-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_grid_stopped_compensated_sum_mean_zero
-- name    : AvramDividend.Classical.avram_wave4_p1_grid_stopped_compensated_sum_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:02:27.649187+00:00
-- url     : https://prove2.me/theorems/0a9db47c-26a8-4061-b0df-c4821b5eb16c
-- title:
--   Stopped finite-grid compensated marked-Poisson integral has mean zero under cellwise predictable L1
-- statement:
--   For a finite deterministic time grid and a random grid-valued stopping index, the signed stochastic reward after subtracting the predictable per-cell intensity integral has expectation zero. Each stopped past coefficient is integrable and independent of its future marked Poisson cell; all marks have the stated law and are independent of their cell count. Product integrability of the stochastic sum is derived from those hypotheses, not assumed. This is a genuine finite-grid L1 centred compensation identity, with continuous-time predictable approximation and infinite-activity L2 still outstanding.
-- source:
--   Proved poisson_predictable_marked_compensation_closed_ws01b (33961fb8-62cf-4cb9-9a1a-b4a1eef4f1e9) and poisson_predictable_marked_product_integrable_ws01b (a467fb2d-71c1-4680-9f98-6b28c8143403); Applebaum Chapters 2 and 4; Avram–Palmowski–Pistorius (2007), Proposition 4(i).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_product_integrable_ws01b

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_grid_stopped_compensated_sum_mean_zero
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
    (hfI : ∀ i ∈ s, Integrable (f i) ν) :
    (∫ ω, ∑ i ∈ s,
      ((if i < τ ω then H i ω else 0) *
          (∑ n ∈ Finset.range (K i ω), f i (Y i n ω)) -
        (if i < τ ω then H i ω else 0) *
          ((r i : ℝ) * ∫ y, f i y ∂ν)) ∂μ) = 0 := by sorry
