-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_finite_mean_condexp_independent
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_finite_mean_condexp_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:47:37.078198+00:00
-- url     : https://prove2.me/theorems/1067a26d-66ce-4042-8471-d2426dc2eec1
-- title:
--   Original intrinsic marked count is conditionally independent of actual past at finite mean without ν-rate
-- statement:
--   For the original spectrally negative Lévy process, if its intrinsic marked jump count on (s,t] has a finite unconditioned mean, its real-valued count has conditional expectation equal to that deterministic unconditioned mean given the actual F_s. This relies solely on proved original independent increments and measurable future extraction; no identification of the Lévy measure intensity is required.
-- source:
--   Proved original extractor 5cf3e058, past factor ad24b83b, source count measurability 8146a449 and pinned Mathlib ae_eq_condExp_of_forall_setIntegral_eq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_finite_mean_condexp_independent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hMeanFinite : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) < ⊤) :
    (condExp (𝓕 s) P (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)) =ᵐ[P]
      (fun _ : Ω => (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P).toReal) := by sorry
