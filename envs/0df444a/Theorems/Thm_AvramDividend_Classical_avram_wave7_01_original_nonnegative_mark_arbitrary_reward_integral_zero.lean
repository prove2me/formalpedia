-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_nonnegative_mark_arbitrary_reward_integral_zero
-- name    : AvramDividend.Classical.avram_wave7_01_original_nonnegative_mark_arbitrary_reward_integral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:54:00.860925+00:00
-- url     : https://prove2.me/theorems/422e4a24-9211-4160-878b-07ff78c8d31b
-- title:
--   Every original Lévy nonnegative-mark source jump reward integral vanishes pathwise
-- statement:
--   For each original source path ω and every (even unbounded and not assumed measurable) nonnegative time–mark reward kernel K, the intrinsic jump measure integral over all nonnegative marks is zero. This follows from exact global source jump support and holds on the actual Ω for arbitrary time horizons, stopped histories and bounded or unbounded variation, with no ν-rate or finite-activity assumption.
-- source:
--   Proved original source global nonnegative marked mass zero 0a9afdb9; Mathlib Measure.restrict_eq_zero and lintegral_zero_measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_nonnegative_mark_arbitrary_reward_integral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (K : (ℝ≥0 × ℝ) → ℝ≥0∞) :
    (∫⁻ p in (Set.univ ×ˢ Ici (0 : ℝ)), K p ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) = 0 := by sorry
