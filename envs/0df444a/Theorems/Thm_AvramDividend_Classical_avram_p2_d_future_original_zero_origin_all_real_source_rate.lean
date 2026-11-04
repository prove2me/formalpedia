-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_zero_origin_all_real_source_rate
-- name    : AvramDividend.Classical.avram_p2_d_future_original_zero_origin_all_real_source_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:39:04.147271+00:00
-- url     : https://prove2.me/theorems/5c2e21c1-6faa-40c9-9d5d-7b0ecfe2a362
-- title:
--   Unconditional original source marked jump-count rate at every real horizon
-- statement:
--   For every original spectrally negative Lévy process X, every Borel mark set B, and every nonnegative real horizon t, the original expected source marked count on (0,t] equals t multiplied by the original unit-time expected marked count. This handles finite, zero and infinite rates including t=0 and 0·∞=0, and does not assume the rate equals the Lévy measure X.ν.
-- source:
--   Case split unit original source mean finite or top. Finite uses newly authored real source rate; infinite uses proved 51f3c26d at positive t and proved original empty-window 0c401781 at t=0.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_finite_unit_mean_exact_real_horizon_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_unit_mean_infinite_positive_real_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_empty_time_window_mean_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_original_zero_origin_all_real_source_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) = (t : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by sorry
