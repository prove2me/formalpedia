-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_mark_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_mark_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:11:06.181479+00:00
-- url     : https://prove2.me/theorems/01d52b72-21f0-4034-93ab-94ee2de890d8
-- title:
--   Countable disjoint Borel marked-cell compensation for weighted true-original Lévy jump counts
-- statement:
--   Expected original true marked jump count weighted by any nonnegative measurable random H over the union of countably many disjoint Borel mark sets equals the sum of each weighted expected count. No ν-intensity, adaptedness or finite rate requirement.
-- source:
--   True original marked measure, MeasureTheory.measure_iUnion, ENNReal.tsum_mul_left, MeasureTheory.lintegral_tsum, original intrinsic rectangle measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_mark_lintegral
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : ι → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hDisj : Pairwise (Function.onFun Disjoint B))
    (H : Ω → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (⋃ i, B i)) ∂P) =
    ∑' i, (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B i)) ∂P) := by sorry
