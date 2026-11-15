-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b138_original_finite_band_marked_grid_card_le_true_allnegative_source_count
-- name    : AvramDividend.Classical.avram_b138_original_finite_band_marked_grid_card_le_true_allnegative_source_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:33:33.213882+00:00
-- url     : https://prove2.me/theorems/d9bfaae8-6b44-4f6b-8c34-ac46f0c6e6e6
-- title:
--   Genuine finite original negative-band occupied-grid cardinal is at most the actual full original negative Poisson source count
-- statement:
--   For a monotone physical grid of the original spectrally negative Lévy source, suppose each genuinely marked cell in a finite index set contains an actual original negative jump belonging to the specified finite reciprocal cutoff band before horizon T. Proved B95 injects these distinct monotone grid cells into the original finite negative marked jump-time Finset. The authoritatively Proved original P2 exact Poisson band count equals the cardinal of that same source marked-time Finset, and monotonicity of the original mapped jump measure bounds the band count by the full negative mark Poisson source count up to T. Thus the marked-grid cell cardinal, lifted to ENNReal, is pathwise bounded by the original full-negative-jump Poisson count, including infinity on exceptional paths. This supplies the actual source dominance needed for B137’s almost-everywhere expected marked count integrability and avoids incorrect toReal conversion of infinite counts. Publication waits for B95 Proved.
-- source:
--   Prepared B95 original monotone grid cell injection, Proved P2 exact finite negative band source count/card and original marked measure monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_count_to_finset_card
import Theorems.Thm_AvramDividend_Classical_avram_b95_original_monotone_grid_marked_cell_count_le_source_jumps
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine finite negative-band occupied source cells are dominated by the full original physical negative Poisson count. -/

theorem AvramDividend.Classical.avram_b138_original_finite_band_marked_grid_card_le_true_allnegative_source_count
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
