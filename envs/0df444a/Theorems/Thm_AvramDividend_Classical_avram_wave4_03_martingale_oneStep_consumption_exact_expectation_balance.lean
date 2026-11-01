-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_martingale_oneStep_consumption_exact_expectation_balance
-- name    : AvramDividend.Classical.avram_wave4_03_martingale_oneStep_consumption_exact_expectation_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:20:34.29495+00:00
-- url     : https://prove2.me/theorems/db079c5b-d6e0-4006-98da-0a72545a6ad5
-- title:
--   Exact one-step martingale expectation budget for bounded adapted control consumption
-- statement:
--   For an actual integrable martingale M and a bounded adapted control weight B on the same filtration and a finite measure, the expected one-step consumption M_t(B_s−B_t) equals the difference between the initial and final expected wealth M_s B_s−M_t B_t. Its key nontrivial step uses the actual martingale conditional expectation and measurability of B_s to prove E[B_s M_t]=E[B_s M_s]. This is an exact discrete stochastic identity, allowing finite-grid telescoping before a separate Stieltjes limit and accommodating right-dividend atoms in B_t=exp(−θD_{t+}); it does NOT assert the full continuous-time controlled Lévy Itô formula.
-- source:
--   Pinned Mathlib Martingale, condExp_mul_of_aestronglyMeasurable_left, integral_condExp; accepted bounded-adapted-weight martingale technique c1efb6e8. Supports source-X Lévy exponential martingale plus postpayment result fab320c3.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_martingale_oneStep_consumption_exact_expectation_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M 𝓕 μ)
    (B : ℝ≥0 → Ω → ℝ) (hB : Adapted 𝓕 B)
    (hBbound : ∀ t ω, 0 ≤ B t ω ∧ B t ω ≤ 1)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, M t ω * (B s ω - B t ω) ∂μ) =
      (∫ ω, B s ω * M s ω ∂μ) -
        (∫ ω, B t ω * M t ω ∂μ) := by sorry
