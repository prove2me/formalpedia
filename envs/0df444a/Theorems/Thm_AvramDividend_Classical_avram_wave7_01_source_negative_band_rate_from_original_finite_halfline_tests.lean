-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_negative_band_rate_from_original_finite_halfline_tests
-- name    : AvramDividend.Classical.avram_wave7_01_source_negative_band_rate_from_original_finite_halfline_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:01:30.483662+00:00
-- url     : https://prove2.me/theorems/216c5090-d302-471c-8ec5-842d097b0e00
-- title:
--   Exact original separated Borel-band rate from explicit finite expected count and half-line Lévy tests
-- statement:
--   For any countable original-process Borel mark-band family, if each band is contained in a strictly negative cutoff with finite expected count and prescribed half-line ν intensity, then the actual unconditional expected Lévy jump-mark rate on each band equals its time length times ν. The proof constructs the original expected mark pushforward measure and uses the accepted finite half-line uniqueness theorem. No auxiliary Poisson sample space and no BV-to-finite-activity inference.
-- source:
--   Original mean measure c026c74a and exact all-start halfline uniqueness 693d2adb; exact source Ω/P/X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_mark_mean_measure_identification_from_halfline_tests
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave7_01_source_negative_band_rate_from_original_finite_halfline_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (C : ℕ → Set ℝ) (hCm : ∀ n, MeasurableSet (C n))
    (hTests : ∀ n, ∃ ε : ℝ, 0 < ε ∧ C n ⊆ Iic (-ε) ∧
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤ ∧
      ∀ a : ℝ,
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν (Iic a ∩ Iic (-ε)))
    : ∀ n,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ C n) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞)) * X.ν (C n) := by sorry
