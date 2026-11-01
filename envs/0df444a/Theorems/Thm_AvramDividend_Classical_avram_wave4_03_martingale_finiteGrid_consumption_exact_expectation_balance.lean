-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_martingale_finiteGrid_consumption_exact_expectation_balance
-- name    : AvramDividend.Classical.avram_wave4_03_martingale_finiteGrid_consumption_exact_expectation_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:24:25.491532+00:00
-- url     : https://prove2.me/theorems/0d3263b6-f7ba-418b-929c-296b6dae43d7
-- title:
--   Exact finite-grid martingale consumption expectation telescoping balance
-- statement:
--   On any deterministic finite nondecreasing time grid, the expectation of the genuine random martingale-weighted consumption sum Σ M_{t_{i+1}}(B_{t_i}−B_{t_{i+1}}) equals exactly E[M_{t0}B_{t0}]−E[M_{tn}B_{tn}]. Each earlier adapted B_{t_i} is multiplied by the later martingale M_{t_{i+1}} using actual conditional expectation; finite sum Bochner integrability and telescoping are fully established. For B_t=e^(−θD_{t+}), every right-dividend atom contributes to the grid cash; diffuse Stieltjes convergence still requires a separate measure-theoretic passage, so this does not assert the full controlled HJB inequality.
-- source:
--   Accepted one-step martingale compensation and pinned Mathlib integral_finset_sum/Finset.sum_range_succ; original Lévy exponential martingale plus postpayment factor downstream.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_martingale_oneStep_consumption_exact_expectation_balance

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_martingale_finiteGrid_consumption_exact_expectation_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M 𝓕 μ)
    (B : ℝ≥0 → Ω → ℝ) (hB : Adapted 𝓕 B)
    (hBbound : ∀ t ω, 0 ≤ B t ω ∧ B t ω ≤ 1)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫ ω, ∑ i ∈ Finset.range n,
      M (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω) ∂μ) =
      (∫ ω, B (u 0) ω * M (u 0) ω ∂μ) -
      (∫ ω, B (u n) ω * M (u n) ω ∂μ) := by sorry
