-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_separated_borel_mark_mean_le_negative_halfline_mean
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_separated_borel_mark_mean_le_negative_halfline_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:00:42.480028+00:00
-- url     : https://prove2.me/theorems/7defd77e-66e2-449a-ad34-b8639e895667
-- title:
--   Original separated Borel marked jump mean is bounded by the negative halfline moment envelope
-- statement:
--   For the literal intrinsic jump-counting measure of the original spectrally negative Lévy process, a bound M on the expected jump count in (0,T] times the closed negative halfline (-infinity,-epsilon] also bounds the expected count for every mark set B contained in that halfline. This follows pathwise from measure monotonicity and then from ENNReal lintegral monotonicity, preserving the exact source and not assuming a Lévy rate, stationarity or finite activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_original_separated_borel_mark_mean_le_negative_halfline_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (ε : ℝ) (hBsep : B ⊆ Iic (-ε)) (M : ℝ≥0∞)
    (hMean : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ∂P) ≤ M) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) ≤ M := by sorry
