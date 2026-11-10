-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus14_original_window_filter_card
-- name    : AvramDividend.Classical.avram_mix_annulus14_original_window_filter_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:39:23.415201+00:00
-- url     : https://prove2.me/theorems/fa9ef32b-6443-48c4-8b2d-e87c2adfc5e5
-- title:
--   Original physical annulus window count is a filtered finite set of actual jump times
-- statement:
--   For the original spectrally negative Levy process, the number of actual jump times in a chronological half-open window with marks in the finite negative annulus equals the filtered cardinal of the finite full-cutoff marked jump-time set. This supplies exact endpoint and same-cell counting for the physical factorial second moment theorem.
-- source:
--   Exact original physical marked jump count-to-encard bridge 2c942e8f and original full-cutoff marked-time finiteness e5e6f70b; deterministic set filter, including Ioc annulus endpoints. Parent factorial 6ea0212e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus14_original_window_filter_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (n m : ℕ) (hnm : n ≤ m) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) =
    (((avram_wave7_06_original_negative_band_marked_times_finite X ω T m).toFinset.filter
      (fun u => s < u ∧ u ≤ t ∧
        -(1 / ((n : ℝ) + 1)) <
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)).card : ℝ≥0∞) := by sorry
