-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_adapted_from_past_event_rate
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_adapted_from_past_event_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:41:32.959555+00:00
-- url     : https://prove2.me/theorems/f76421c7-db3a-4cc7-83c1-1d8d81384833
-- title:
--   Original intrinsic Lévy future marked weighted rate from genuine past-event rate
-- statement:
--   For the actual original spectrally negative Lévy source and unchanged probability measure, an exact marked future rectangle first-moment rate on every event of the genuine past filtration transfers to any nonnegative adapted ENNReal weight. The original event moment is explicitly assumed rather than replacing it with an auxiliary Poisson process or an unproved zero-origin Lévy ν-rate. Reuses the already-Proved original intrinsic-count measurability and separately accepted ambient indicator-to-weight theorem.
-- source:
--   Proved original count-measurable d9c55240 and ambient ENNReal extension 419a95ae. Useful direct W7-06 event-to-adapted transition while P2-A separately proves the ν rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_ambient_indicator_to_past_weight_lintegral

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_adapted_from_past_event_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) (r : ℝ≥0∞)
    (hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) = P A * r)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
    (∫⁻ ω, H ω ∂P) * r := by sorry
