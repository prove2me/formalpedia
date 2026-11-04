-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_zero_mean_adapted_weight_count_zero
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_zero_mean_adapted_weight_count_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:13:09.420245+00:00
-- url     : https://prove2.me/theorems/0ef4fdf2-73c7-46c0-8c7e-fb212b4536ac
-- title:
--   Zero expected original marked jump contribution of any zero-mean past-adapted weight, including infinite unconditional rates
-- statement:
--   Any nonnegative original-past-measurable weight with zero first moment has zero expected product with the genuine original marked jump count over an ordered (s,t] interval. This remains valid when the unconditional future marked-count expectation is infinite, using the native zero-times-infinity semantics of ENNReal and the accepted original future/past factorisation.
-- source:
--   Accepted original exact (s,t] future/past product 7090fa21-7f82-4913-ab72-882c2c3aa0bc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_Ioc_st_future_past_factor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_zero_mean_adapted_weight_count_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (hZero : (∫⁻ ω, H ω ∂P) = 0) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) = 0 := by sorry
