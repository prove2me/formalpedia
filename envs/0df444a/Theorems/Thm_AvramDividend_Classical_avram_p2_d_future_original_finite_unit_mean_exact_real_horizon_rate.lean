-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_finite_unit_mean_exact_real_horizon_rate
-- name    : AvramDividend.Classical.avram_p2_d_future_original_finite_unit_mean_exact_real_horizon_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:34:45.917893+00:00
-- url     : https://prove2.me/theorems/ebc19ca0-26ef-45e2-b594-10c891b72f88
-- title:
--   Original marked jump source mean has exact all-real-time rate whenever its unit mean is finite
-- statement:
--   For the unchanged original spectrally negative Lévy process and exact source restricted and mapped jump-count measure, if the expected number of marks in B over the unit interval is finite, then the source expected marked count on (0,t] equals t times that same unit mean for every real nonnegative t. This proves source-derived real-time intensity, without identifying the rate with X.ν.
-- source:
--   Combine Proved 243bfabc finite mean, 659c56d0 rational grid, 1b0514e9 original rational expected-count sandwich, and the independently authored ENNReal finite mesh squeeze. Every time/count bracket uses the same n.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_finite_unit_mean_all_real_horizons_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_nnreal_rational_grid_enclosure
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_rational_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_ennreal_finite_mesh_squeeze

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_original_finite_unit_mean_exact_real_horizon_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) (hunit : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) < ⊤) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) =
      (t : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by sorry
