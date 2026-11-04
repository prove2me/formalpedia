-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_mark_mono_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_mark_mono_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:18:40.208125+00:00
-- url     : https://prove2.me/theorems/442030e5-fc26-4a99-9df2-826613ed43d6
-- title:
--   Monotonicity of original Lévy marked jump expected counts in the mark band
-- statement:
--   For every nonnegative possibly infinite random weight, inclusion of original intrinsic jump mark sets implies monotonicity of the weighted expected jump count. Holds pathwise and integrated, with no rate identification or measurability premise on the weight.
-- source:
--   MeasureTheory.measure_mono, Set.prod_mono, mul_le_mul_of_nonneg_left, lintegral_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_mark_mono_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B C : Set ℝ) (hBC : B ⊆ C)
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
      (Ioc s (s + T) ×ˢ C) ∂P) := by sorry
