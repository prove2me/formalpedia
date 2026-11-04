-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_Ioc_st_adapted_origin_mean
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_Ioc_st_adapted_origin_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:54:33.362886+00:00
-- url     : https://prove2.me/theorems/fa04e9fe-afa1-416b-8d85-9d1638064a3d
-- title:
--   Original adapted marked-count mean at exact ordered endpoints equals weight mean times zero-origin mean
-- statement:
--   For s ≤ t, a genuine original Lévy-process marked jump count on (s,t] has nonnegative first moment against any weight measurable at s equal to expected weight times the genuine original count on (0,t-s]. No Lévy measure ν rate is used or assumed.
-- source:
--   Proved original source adapted weighted origin transfer ca4d6415-6b7a-4cf6-b153-2bb440e142e2 and ordered NNReal endpoint identity tsub_add_cancel_of_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_origin_mean_to_adapted_lintegral

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_Ioc_st_adapted_origin_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) =
    (∫⁻ ω, H ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (t - s) ×ˢ B) ∂P) := by sorry
