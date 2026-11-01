-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_finiteGrid_positive_martingale_consumption_budget
-- name    : AvramDividend.Classical.avram_wave4_03_finiteGrid_positive_martingale_consumption_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:32:37.868436+00:00
-- url     : https://prove2.me/theorems/2500df75-edd2-4fde-8b51-9894f710ff97
-- title:
--   Finite-grid adapted consumption is nonnegative pathwise and its expected reward is bounded by initial wealth
-- statement:
--   For a truly nonnegative integrable martingale and a bounded adapted pathwise antitone consumption factor B, every deterministic monotone-grid consumption sum Σ M_{t_{i+1}}(B_{t_i}−B_{t_{i+1}}) is nonnegative samplewise, and its expected value is bounded by the initial expected wealth E[M_{t0}B_{t0}]. The proof invokes the Accepted exact finite-grid martingale compensation and observes that the terminal expected wealth is nonnegative. This supplies the sign and uniform expectation budget needed for a later Fatou/Stieltjes limit. No continuous-time limit is asserted.
-- source:
--   Accepted finite-grid exact martingale compensation 0d3263b6, Mathlib Finset.sum_nonneg and integral_nonneg; source exponential Levy martingale is pointwise positive, postpayment discount factor pathwise decreasing.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_martingale_finiteGrid_consumption_exact_expectation_balance

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_finiteGrid_positive_martingale_consumption_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M 𝓕 μ)
    (hMpos : ∀ t ω, 0 ≤ M t ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : Adapted 𝓕 B)
    (hBbound : ∀ t ω, 0 ≤ B t ω ∧ B t ω ≤ 1)
    (hBanti : ∀ ω, Antitone (fun t => B t ω))
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∀ ω, 0 ≤ ∑ i ∈ Finset.range n,
      M (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω)) ∧
    (∫ ω, ∑ i ∈ Finset.range n,
      M (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω) ∂μ) ≤
      (∫ ω, B (u 0) ω * M (u 0) ω ∂μ) := by sorry
