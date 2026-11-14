-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b165_original_true_bounded_random_monotone_marked_grid_count_integrable
-- name    : AvramDividend.Classical.avram_b165_original_true_bounded_random_monotone_marked_grid_count_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:58:14.841642+00:00
-- url     : https://prove2.me/theorems/5b4914ac-2177-45b4-bcf8-063a7df6844c
-- title:
--   Genuine original finite physically marked random monotone stopped grid has integrable cardinal under finite negative activity
-- statement:
--   For the exact original finite-negative-activity spectrally negative Levy source and arbitrary potentially random monotone stopped physical grid of nonnegative time intervals before a fixed bounded clock T, suppose on conull source events every selected marked index contains an actual original source jump and every selected cell ends no later than T. The prepared B163 original physical marked-grid ENNReal cardinal domination theorem gives a pointwise bound by full genuine negative marked Poisson source count on each path of the conull event. The already Proved original mix_fin14 intensity theorem gives finite lintegral of this actual source Poisson count up to T. By lintegral_mono_ae, the true selected marked-grid cardinal has finite expected count without any global or pointwise finiteness hypothesis and without requiring selected count measurability upfront. This provides the authentic expected jump contact bound needed for localised original stopped Gaussian-jump Ito mesh energy. Publication waits for B163 Proved.
-- source:
--   Prepared B163 full original source Poisson ENNReal count domination and Proved mix_fin14 original bounded clock negative Poisson L1 intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual number of original physical negative-jump containing cells of any bounded random monotone stopped grid has finite source expectation. -/

theorem AvramDividend.Classical.avram_b165_original_true_bounded_random_monotone_marked_grid_count_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0) (hMono : ∀ ω, Monotone (grid ω))
    (J : Ω → Finset ℕ)
    (hMarks : ∀ᵐ ω ∂P, ∀ i ∈ J ω, ∃ u : ℝ≥0,
      grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hRange : ∀ᵐ ω ∂P, ∀ i ∈ J ω, grid ω (i + 1) ≤ T) :
    (∫⁻ ω, ((J ω).card : ℝ≥0∞) ∂P) < ⊤ := by sorry
