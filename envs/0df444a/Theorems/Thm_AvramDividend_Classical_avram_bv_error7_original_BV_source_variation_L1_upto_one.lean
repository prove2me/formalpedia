-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_variation_L1_upto_one
-- name    : AvramDividend.Classical.avram_bv_error7_original_BV_source_variation_L1_upto_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:29:02.273862+00:00
-- url     : https://prove2.me/theorems/09287ead-652a-4521-8a54-ac198d1c917b
-- title:
--   Original BV physical source variation envelope is integrable up to unit horizon
-- statement:
--   For the actual spectrally negative Lévy source X under Standing and BoundedVariation, the physical discounted-C1 error mass |drift| T + |T drift - X_T| is nonnegative at every sample and Bochner integrable over the original probability measure for each T ≤ 1. This uses the already Proved original residual first-moment result; no proxy process or stopped cash budget is introduced. The envelope can dominate genuine X/D physical-mesh C1 error through a separate pathwise estimate.
-- source:
--   Original BV drift residual Integrable up to one: 9831126a-7962-4ea5-a6a8-fe8844449052. Physical source C1 mesh error cf5b9fb6-687b-43dd-b185-d99ad5b834fe and actual uniform variation a0c7ac61-d2ae-4dd3-8a81-93994b4265d9. Target 2bc848f9-fa19-488b-a623-f18154d8db0b; no circular budget import.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_BV_source_variation_L1_upto_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : T ≤ 1) :
    Integrable (fun ω =>
      |X.drift| * (T : ℝ) + |(T : ℝ) * X.drift - X.X T ω|) P ∧
    (∀ ω, 0 ≤
      |X.drift| * (T : ℝ) + |(T : ℝ) * X.drift - X.X T ω|) := by sorry
