-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_pairwise_time_rectangles_tsum_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_pairwise_time_rectangles_tsum_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:48:36.895788+00:00
-- url     : https://prove2.me/theorems/8a93a926-0838-4526-b471-670d2f191150
-- title:
--   Weighted source Lévy countable compensation-ready additivity across disjoint time rectangles
-- statement:
--   The original Lévy jump count on pairwise disjoint future time windows, with independently varying Borel marks, satisfies countable additive expectation for any nonnegative measurable path weight. The identity is valid with zero-times-infinity and without a source Lévy rate.
-- source:
--   Proved original pathwise disjoint time-rectangle additivity, intrinsic source rectangle measurability, ENNReal.tsum_mul_left, Mathlib MeasureTheory.lintegral_tsum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_pairwise_time_rectangles_tsum_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℕ → ℝ≥0) (B : ℕ → Set ℝ)
    (hB : ∀ n, MeasurableSet (B n))
    (hTimeDisj : Pairwise (fun i j =>
      Disjoint (Ioc (s i) (s i + T i))
        (Ioc (s j) (s j + T j))))
    (H : Ω → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (⋃ n, Ioc (s n) (s n + T n) ×ˢ B n) ∂P) =
    ∑' n, (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s n) (s n + T n) ×ˢ B n) ∂P) := by sorry
