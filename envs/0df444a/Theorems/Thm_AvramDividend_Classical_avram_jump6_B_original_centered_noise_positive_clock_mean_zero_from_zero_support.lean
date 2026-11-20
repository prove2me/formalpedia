-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_centered_noise_positive_clock_mean_zero_from_zero_support
-- name    : AvramDividend.Classical.avram_jump6_B_original_centered_noise_positive_clock_mean_zero_from_zero_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:24:16.451313+00:00
-- url     : https://prove2.me/theorems/e0093b88-7f5a-4e2f-ab84-2cabe0b76ca4
-- title:
--   True positive stopped-clock event preserves unconditional compensated source mean zero when noise vanishes on zero clock
-- statement:
--   For a measurable original stopped clock sigma and integrable centred compensated stochastic source M with E[M]=0, if M is pathwise zero on the complementary zero-clock paths, the expectation restricted to the true event sigma>0 remains zero. This resolves the event-centring transfer used by the original positive-clock expected budget without incorrectly assuming that an arbitrary future-dependent event preserves mean zero.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_centered_noise_positive_clock_mean_zero_from_zero_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (σ : Ω → ℝ≥0) (hσmeas : Measurable σ)
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hMzero : ∀ ω, σ ω = 0 → M ω = 0)
    (hMmean : (∫ ω, M ω ∂P) = 0) :
    (∫ ω in {ω | 0 < σ ω}, M ω ∂P) = 0 := by sorry
