-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a184_nonnegative_real_expected_L1_zero_of_extended_integral_zero
-- name    : AvramDividend.Classical.avram_ga_a184_nonnegative_real_expected_L1_zero_of_extended_integral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T15:51:57.880688+00:00
-- url     : https://prove2.me/theorems/acf58a6d-a0b6-4eec-b175-625d1c50c8c3
-- title:
--   Nonnegative integrable real observables with extended expectations tending to zero have real expectations tending to zero
-- statement:
--   On any measure space, for a sequence of integrable, almost surely nonnegative real observables, if their extended nonnegative integrals converge to zero then their ordinary real expectations also converge to zero. This is the exact bridge needed to turn the Proved original Gaussian stopped raw large-tail result ga56 into the expected L1 tail term for the genuine full-cell Taylor remainder a149.
-- source:
--   Mathlib ofReal_integral_eq_lintegral_ofReal and ENNReal.tendsto_toReal continuous at zero.

import Mathlib
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a184_nonnegative_real_expected_L1_zero_of_extended_integral_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℕ → Ω → ℝ)
    (hI : ∀ m, Integrable (T m) P)
    (hNonneg : ∀ m, ∀ᵐ ω ∂P, 0 ≤ T m ω)
    (hL : Tendsto (fun m => ∫⁻ ω, ENNReal.ofReal (T m ω) ∂P)
      atTop (𝓝 (0 : ℝ≥0∞))) :
    Tendsto (fun m => ∫ ω, T m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
