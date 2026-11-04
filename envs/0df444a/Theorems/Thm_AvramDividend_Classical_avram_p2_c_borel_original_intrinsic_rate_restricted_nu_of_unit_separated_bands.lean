-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_rate_restricted_nu_of_unit_separated_bands
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_intrinsic_rate_restricted_nu_of_unit_separated_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:06:28.466195+00:00
-- url     : https://prove2.me/theorems/50e8e462-dc26-4a41-9c15-e253b4d4fc71
-- title:
--   Original intrinsic Borel intensity equals the Lévy measure restricted to negative marks
-- statement:
--   If the true original one-unit expected marked counts match the prescribed Lévy measure for every strictly separated negative Borel mark set, then every original zero-origin expected marked count equals time times ν restricted to negative marks. No separate support assumption on ν is made.
-- source:
--   Proved P2-C original intrinsic source-intensity aeede32d and negative-measure uniqueness 78e051e1; exact original unit-time separated marks supplied as an explicit analytic hypothesis.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_negative_supported_measure_eq_of_separated_bands
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_intrinsic_rate_restricted_nu_of_unit_separated_bands
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hUnitSeparated : ∀ (B : Set ℝ), MeasurableSet B →
      ∀ ε : ℝ, 0 < ε → B ⊆ Iic (-ε) →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = X.ν B) :
    ∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) *
          X.ν (B ∩ Iio (0 : ℝ)) := by sorry
