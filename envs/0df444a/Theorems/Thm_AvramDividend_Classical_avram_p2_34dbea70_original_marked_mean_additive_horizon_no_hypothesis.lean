-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:48:23.642344+00:00
-- url     : https://prove2.me/theorems/d20e4c7e-90a5-493b-8e9a-19fb04ddb4cd
-- title:
--   Original intrinsic Borel marked-jump expected count is additive in elapsed time without extra assumptions
-- statement:
--   For every actual original spectrally negative Lévy process, nonnegative horizons T and S, and Borel mark set B, the intrinsic expected marked-jump count over (0,T+S] equals the sum of the intrinsic expected marked-jump counts over (0,T] and (0,S]. The result combines the already-Proved exact original source count measurability, original stationary mean, and deterministic marked-rectangle additivity. No rate, compensator or extra measurability assumption is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_intrinsic_band_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_stationary_marked_mean_additive_horizon

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T S : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (T + S) ×ˢ B) ∂P) =
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) +
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 S ×ˢ B) ∂P) := by sorry
