-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_mark_rate_band_integrable
-- name    : AvramDividend.Classical.avram_p2_j_ui_public_original_mark_rate_band_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:47:28.709599+00:00
-- url     : https://prove2.me/theorems/88d898da-6069-4433-bf54-94e7a1cee923
-- title:
--   Original intrinsic jump intensity integrates every bounded separated-band real test
-- statement:
--   The original-process intrinsic mark-rate measure constructed by the source Borel intensity theorem has finite negative separated-band mass. Every measurable real mark test bounded in absolute value by a constant on such a band and vanishing outside is Bochner integrable against that same intrinsic mark-rate measure. The witness retains the actual original marked-count rate for every Borel set and every time horizon.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_public_original_mark_rate_band_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ)
    (hbound : ∀ y : ℝ,
      ‖f y‖ ≤ (Set.Iic (-ε)).indicator (fun _ : ℝ => C) y) :
    ∃ markRate : Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Set.Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) * markRate B) ∧
      Integrable f markRate := by sorry
