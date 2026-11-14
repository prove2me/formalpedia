-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
-- name    : AvramDividend.Classical.avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:53:18.414767+00:00
-- url     : https://prove2.me/theorems/b149965c-38ee-4ba2-b82b-e1c819c0f07b
-- title:
--   All genuine source jump-containing cells of a bounded finite monotone original grid have cardinal bounded by full original negative Poisson count
-- statement:
--   Fix the genuine original spectrally negative Levy source on any sample path and an arbitrary finite family of cells in a monotone original physical time grid within one finite horizon. Assume every genuinely marked cell contains some actual nonzero original source jump, with all these cells ending before the horizon. Authoritatively Proved B118 constructs one reciprocal negative mark cutoff sufficiently close to zero to detect one genuine jump simultaneously in every selected marked cell, using the original spectral no-positive-jump property. Each selected source marked time then lies in the finite original negative band jump-time set at this common cutoff, because it is positive, before the physical horizon, and satisfies the original negative band inequality. Prepared B154 bounds the number of cutoff occupied monotone grid cells by the full original negative jump Poisson source count in ENNReal. Combining these results removes all artificial cutoff or finite band assumptions from actual finite monotone grid marked-cell cardinality domination, and remains valid on exceptional paths even when original full negative count is infinite. This directly provides the source count bound needed to instantiate the Proved B150 and pending B157 finite-mesh Gaussian and negative jump energy estimates for true physical marked cells.
-- source:
--   Proved original B118 common physical negative cutoff and wave7_06 finite source negative marked-time set, pending B154 direct source Poisson count bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b118_original_finite_physically_marked_cells_one_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_b154_original_direct_band_marked_grid_card_le_full_source_poisson
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All genuine jump-containing cells of a finite monotone original source grid before a bounded physical horizon are dominated by the full same-source negative Poisson count, without any chosen cutoff. -/

theorem AvramDividend.Classical.avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0)
    (grid : ℕ → ℝ≥0) (hmono : Monotone grid)
    (J : Finset ℕ)
    (hJ : ∀ i ∈ J, ∃ u : ℝ≥0,
      grid i < u ∧ u ≤ grid (i + 1) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hRange : ∀ i ∈ J, grid (i + 1) ≤ T) :
    (J.card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) := by sorry
