-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_singleton_time_atom_lintegral_zero
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_singleton_time_atom_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:55:34.550224+00:00
-- url     : https://prove2.me/theorems/840b78ed-5007-4f9e-9ed3-35f865ac272d
-- title:
--   The original Lévy singleton-time jump count has zero integral under every atomless time measure
-- statement:
--   For every actual source sample path and every atomless time measure, the extended nonnegative Lebesgue integral over time of the intrinsic source jump count on singleton slices {t}×B vanishes for any Borel mark band B. No BV or Poisson replacement is used. The exact single-time atom identification and countability of the real source jump times discharge this pathwise Fubini time-section nullity.
-- source:
--   Accepted original path time-null theorem 0ab6cc27, exact original source single-time atom identification 74f501cd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_time_support_lebesgue_null_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_exact

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_singleton_time_atom_lintegral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (νt : Measure ℝ≥0) [NullSingletonClass νt]
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ t : ℝ≥0,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ({t} ×ˢ B) ∂νt) = 0 := by sorry
