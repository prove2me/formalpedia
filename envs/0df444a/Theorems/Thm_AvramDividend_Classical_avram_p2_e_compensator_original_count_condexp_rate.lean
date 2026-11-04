-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_count_condexp_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_count_condexp_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:35:49.75782+00:00
-- url     : https://prove2.me/theorems/b87b82e9-e6bd-4857-b20a-1058981a74b6
-- title:
--   Original intrinsic marked future count has deterministic conditional expectation at its actual past filtration
-- statement:
--   For the actual original spectrally negative Levy process, the real intrinsic marked count on (s,t] has conditional expectation (t-s) ν(B) at the original F_s filtration, assuming finite ν(B) and the explicit unconditional original count rate. The proof uses proved original future extraction and past factorisation plus the uniqueness characterisation of conditional expectation. No conditional law or compensator is assumed.
-- source:
--   Proved original future extractor 5cf3e058, actual past factor ad24b83b, source count measurability 8146a449 and finite-rate real integrability 52b7e6d6; pinned Mathlib ae_eq_condExp_of_forall_setIntegral_eq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_count_condexp_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (condExp (𝓕 s) P (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)) =ᵐ[P]
      (fun _ : Ω => (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) := by sorry
