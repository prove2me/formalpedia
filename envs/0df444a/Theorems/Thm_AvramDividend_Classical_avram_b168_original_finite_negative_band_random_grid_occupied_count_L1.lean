-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b168_original_finite_negative_band_random_grid_occupied_count_L1
-- name    : AvramDividend.Classical.avram_b168_original_finite_negative_band_random_grid_occupied_count_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:54:05.61727+00:00
-- url     : https://prove2.me/theorems/6d8a44e0-5748-4353-88ce-f2c3b9bc8f01
-- title:
--   Genuine bounded random monotone original finite-negative-band source occupied-grid cell count has finite expectation
-- statement:
--   For the genuine original spectrally negative Levy source with finite negative jump intensity, consider a bounded potentially random monotone grid of physical source intervals. On a conull event suppose every cell in a selected finite index set contains an actual original jump whose mark belongs to a fixed finite reciprocal negative cutoff band before the bounded physical horizon T. Pending B154 bounds each selected marked-cell cardinal in ENNReal by the full actual original negative Poisson source count up to T, preserving any infinite count on exceptional paths. The already Proved mix_fin14 original source intensity theorem gives finite expected full negative Poisson count on the bounded clock. Monotonicity of the lintegral almost everywhere concludes finite expected occupied negative-band cell count. This directly closes the jump-contact count L1 input for the original Gaussian and negative-band random-clock source mesh energy without any all-path finiteness or second-moment hypothesis. Publish only when B154 Proved.
-- source:
--   Prepared B154 original physical band occupied source count and Proved original mix_fin14 source intensity first moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The number of actual original negative finite-band jump containing cells of any bounded random monotone stopped grid is integrable under finite negative source activity. -/

theorem AvramDividend.Classical.avram_b168_original_finite_negative_band_random_grid_occupied_count_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n cut : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0) (hMono : ∀ ω, Monotone (grid ω))
    (J : Ω → Finset ℕ)
    (hJ : ∀ᵐ ω ∂P, ∀ i ∈ J ω,
      ∃ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω T cut).toFinset,
        u ∈ Ioc (grid ω i) (grid ω (i + 1))) :
    (∫⁻ ω, ((J ω).card : ℝ≥0∞) ∂P) < ⊤ := by sorry
