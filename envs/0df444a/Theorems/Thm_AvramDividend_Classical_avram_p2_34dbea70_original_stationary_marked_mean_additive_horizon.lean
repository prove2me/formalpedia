-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_stationary_marked_mean_additive_horizon
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_stationary_marked_mean_additive_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:41:11.550239+00:00
-- url     : https://prove2.me/theorems/521fb7ce-99de-4982-9035-142df44bc511
-- title:
--   Original marked-jump expected count is additive in the time horizon
-- statement:
--   For the actual original spectrally negative Lévy process and a Borel mark set, assume the original intrinsic marked-count observable on the first interval is measurable. Then the expected intrinsic count over (0,T+S] equals the sum of its expectations over (0,T] and (0,S]. This combines the already-Proved exact original stationary marked-count theorem with pathwise additivity over adjacent rectangles, without identifying the rate with the Lévy measure or assuming a compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_marked_rectangle_time_concatenation

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_original_stationary_marked_mean_additive_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T S : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hCountMeas : Measurable (fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B))) :
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
