-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_finite_nu_past_real_mean
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_finite_nu_past_real_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:35:34.214565+00:00
-- url     : https://prove2.me/theorems/15ccbd58-8cf6-4219-a287-22666627de2e
-- title:
--   Original finite-intensity marked jump count has prescribed real set integral on every past event
-- statement:
--   Under the original finite Lévy mark intensity and source unconditional marked-rate hypothesis, the real-valued original intrinsic marked jump count integrates over any event in the actual past F_s as P(A) times its expected ν-intensity. This follows from source measurability and the proved future extractor and past factorisation.
-- source:
--   Proved 8146a449 original count measurability, 5cf3e058 original future extractor and ad24b83b past event factor; pinned integral_toReal and ENNReal finite product.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_finite_nu_past_real_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫ ω in A, (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ∂P) =
      (P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal := by sorry
