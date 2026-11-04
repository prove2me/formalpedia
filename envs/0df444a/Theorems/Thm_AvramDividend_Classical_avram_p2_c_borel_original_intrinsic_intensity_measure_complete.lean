-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_intrinsic_intensity_measure_complete
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:12:17.668899+00:00
-- url     : https://prove2.me/theorems/aeede32d-d89b-4abb-9ed8-e0115c7bd59d
-- title:
--   Genuine original negative jump-intensity measure is σ-finite and scales linearly in time
-- statement:
--   The original source process has a canonical intrinsic intensity markRate defined from its expected unit-time marked jump counts. For all Borel marks, the expected actual jump count over (0,T] equals T markRate(B), including infinite activity. markRate is σ-finite, supported on negative marks and finite on all bands bounded away from zero. Identifying markRate with the prescribed Lévy ν is explicitly left as a separate analytic theorem.
-- source:
--   Proved original expected measure σfinite/additive package 7c95a8cd and proved all-real-horizon time scaling 5c2e21c1; no unproved ν equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_expected_measure_sigma_finite_additive_package
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_zero_origin_all_real_source_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_intrinsic_intensity_measure_complete
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ markRate : Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) * markRate B) ∧
      (∀ ε : ℝ, 0 < ε → markRate (Iic (-ε)) < ⊤) ∧
      (∀ (B : Set ℝ), MeasurableSet B →
        markRate B = markRate (B ∩ Iio (0 : ℝ))) ∧
      SigmaFinite markRate := by sorry
