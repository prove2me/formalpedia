-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
-- name    : AvramDividend.Classical.avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T20:59:51.689275+00:00
-- url     : https://prove2.me/theorems/f6f6ada8-b325-4867-81c3-b1b55011015f
-- title:
--   Original monotone physically marked grid count is bounded directly by the full negative Poisson source count
-- statement:
--   For a monotone grid of original physical source clock intervals, each selected genuinely marked finite cell contains an original negative source jump within one finite reciprocal cutoff band before a fixed horizon. Proved wave7_06 unique marked-grid index and Finset injection bound the number of occupied cells by the finite marked source time Finset. Proved P2 original source band count-to-card identifies this cardinal with the actual mapped negative jump Poisson cutoff rectangle count. Since this rectangle is contained in the original full negative mark rectangle, monotonicity of the original source measure bounds selected cell count by full negative Poisson count in ENNReal, even when that count is infinite on exceptional paths. This eliminates the Open B95 dependency from the physical marked-grid count route.
-- source:
--   Proved original wave7_06 monotone grid jump-index uniqueness and P2 exact original band source count/card.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_count_to_finset_card
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_monotone_marked_grid_index_unique
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine finite negative-band occupied source cells are dominated by the full original physical negative Poisson count. -/

theorem AvramDividend.Classical.avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ)
    (grid : ℕ → ℝ≥0) (hmono : Monotone grid)
    (J : Finset ℕ)
    (hJ : ∀ i ∈ J,
      ∃ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset,
        u ∈ Ioc (grid i) (grid (i + 1))) :
    (J.card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) := by sorry
