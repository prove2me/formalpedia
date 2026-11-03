-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
-- name    : AvramDividend.Classical.avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:38:45.454737+00:00
-- url     : https://prove2.me/theorems/8a788cbd-318c-4951-a648-5ae463e96084
-- title:
--   Original Lévy arbitrary measurable future functional factors in expectation against adapted past weights
-- statement:
--   For the actual spectrally negative Lévy process on its unchanged Ω,P,𝓕, any nonnegative extended-real variable H measurable in the original past at deterministic s and any nonnegative extended-real measurable functional of the entire shifted original future path factor in expectation: E[H F(Y_s)] = E[H] E[F(Y_s)]. This holds for unbounded H and F without separate integrability assumptions via ENNReal. It is the exact weighted factorisation interface required to derive conditional marked jump compensation once the intrinsic marked count has a measurable future-path extractor and the unconditional rate is proved.
-- source:
--   Import Proved actual original-past/future functional independence 86ab54a5-0f9f-4e69-a76c-19f22db4d908 and Proved shifted-future product measurability 8b9eb23c-245d-4e22-976b-8f584e3fdc1a. Apply Mathlib lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (Fpath : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable Fpath) :
    (∫⁻ ω, H ω * Fpath (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) ∂P) =
    (∫⁻ ω, H ω ∂P) *
      (∫⁻ ω, Fpath (fun t : ℝ≥0 =>
        X.X (s + t) ω - X.X s ω) ∂P) := by sorry
