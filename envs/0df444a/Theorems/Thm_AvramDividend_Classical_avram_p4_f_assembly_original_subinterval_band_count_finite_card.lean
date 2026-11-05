-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_subinterval_band_count_finite_card
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_subinterval_band_count_finite_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:01:09.159368+00:00
-- url     : https://prove2.me/theorems/8fff1b9c-0bd6-4fed-b621-d23850e2a499
-- title:
--   Original marked negative-jump intrinsic measure on every bounded subinterval equals the exact finite source jump-time filter count
-- statement:
--   For every genuine original spectrally negative Lévy path and every subinterval (s,t] within (0,T], its negative marked intrinsic counting measure equals the extended natural cardinal of those original finite-horizon marked times satisfying s<u≤t. Uses actual original path jumps and the source rectangle measure theorem, with no auxiliary process or stochastic independence assumptions.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_subinterval_band_count_finite_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T s t : ℝ≥0) (hst : t ≤ T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
    ((F.filter (fun u => s < u ∧ u ≤ t)).card : ℝ≥0∞) := by sorry
