-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_zero_horizon_marked_jump_rate
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_zero_horizon_marked_jump_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:06:42.955205+00:00
-- url     : https://prove2.me/theorems/97229fd7-21ba-490b-98a5-7bae412d0c01
-- title:
--   Original intrinsic marked Lévy jump count has exactly zero mean on the zero horizon
-- statement:
--   For the same original spectrally negative Lévy process, intrinsic jump measure and arbitrary mark set B, the marked jump counting measure of the empty time interval (0,0] has zero expected mass. This equals 0 times the original Lévy measure of B even when that measure is infinite. No finite jump activity or compensator assumption is needed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_original_zero_horizon_marked_jump_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 0 ×ˢ B) ∂P) = (0 : ℝ≥0∞) * X.ν B := by sorry
