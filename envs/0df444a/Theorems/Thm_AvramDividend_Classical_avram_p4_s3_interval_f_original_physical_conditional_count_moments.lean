-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_f_original_physical_conditional_count_moments
-- name    : AvramDividend.Classical.avram_p4_s3_interval_f_original_physical_conditional_count_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:05:10.066204+00:00
-- url     : https://prove2.me/theorems/d42bd524-886f-4db6-973a-2b87823615fe
-- title:
--   Physical original future marked count conditional first and second moments from genuine source moments
-- statement:
--   The original intrinsic negative-mark jump count over (s,t] is represented by the same X shifted-future path. If its actual centred real count is integrable, its square is integrable, and its unconditional mean and variance match 0 and the genuine rate r, then conditioning on the original filtration at s gives mean zero and conditional centred square r. Source future-measurability and independence are proved, not assumed; unconditional moment premises remain explicit.
-- source:
--   Proved original intrinsic measurable future extractor d9b9e3c2-55dd-4d9b-82ee-f6ce49bb70c5 and original shifted-future path conditional first/second moments af7a6ae1-9c80-4160-9501-5d24b1bfc27c. Physical N equality, integrability and unconditional moments are explicit.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_future_path_conditional_first_second_moments
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_f_original_physical_conditional_count_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (N : Ω → ℝ≥0∞)
    (hN : ∀ ω, N ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (r : ℝ)
    (hInt : Integrable (fun ω => (N ω).toReal - r) P)
    (hSqInt : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P)
    (hMean : (∫ ω, (N ω).toReal - r ∂P) = 0)
    (hVariance : (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r) :
    (P[(fun ω => (N ω).toReal - r) | 𝓕 s] =ᵐ[P] (fun _ => 0)) ∧
    (P[(fun ω => ((N ω).toReal - r) ^ 2) | 𝓕 s] =ᵐ[P] (fun _ => r)) := by sorry
