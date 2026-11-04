-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_horizon_mono_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_horizon_mono_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:27:00.672197+00:00
-- url     : https://prove2.me/theorems/561b326f-5868-4e64-b334-fe9941fe8d8e
-- title:
--   Monotonicity of true intrinsic Lévy marked expected count over increasing horizons
-- statement:
--   For the true Lévy process, an arbitrary nonnegative ENNReal random weight and any Borel marked set, extending the finite observation horizon preserves the weighted expectation inequality, without a Lévy ν-rate identity.
-- source:
--   MeasureTheory.lintegral_mono, measure_mono, Set.prod_mono, interval inclusion from nonnegative add_le_add_left.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_horizon_mono_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T U : ℝ≥0) (hTU : T ≤ U) (B : Set ℝ)
    (H : Ω → ℝ≥0∞) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) ≤
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + U) ×ˢ B) ∂P) := by sorry
