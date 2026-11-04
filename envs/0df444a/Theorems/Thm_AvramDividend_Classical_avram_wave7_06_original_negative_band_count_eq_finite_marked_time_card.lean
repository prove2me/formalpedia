-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:05:22.767631+00:00
-- url     : https://prove2.me/theorems/f0197436-2681-46a3-8ee4-4df5e3dee1a5
-- title:
--   Actual original negative-band jump count equals finite marked-time cardinal
-- statement:
--   On each actual original Lévy path, the intrinsic marked counting measure of the negative-band rectangle (0,T]×(-∞,-1/(n+1)] equals the finite natural cardinality of original marked jump times in that rectangle. Uses proven original finite separated jump times, no auxiliary process or probabilistic hypothesis.
-- source:
--   W7-06 source-path occupancy representation prerequisite for the Poisson void-rate law and L2 marked-cell compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
    ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard : ℝ≥0∞) := by sorry
