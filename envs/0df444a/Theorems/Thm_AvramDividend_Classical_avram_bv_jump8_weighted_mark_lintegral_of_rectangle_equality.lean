-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
-- name    : AvramDividend.Classical.avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:44:50.267714+00:00
-- url     : https://prove2.me/theorems/68109213-714d-4198-9954-a561a139d74c
-- title:
--   Equality on all measurable marked time rectangles determines every nonnegative Borel weighted marked integral
-- statement:
--   For arbitrary marked measures, equality of all time-window Borel mark rectangle masses implies equality of integrals of an arbitrary measurable nonnegative weight depending only on the jump mark. This follows from equality of the two restricted mark pushforwards and measurable integration. No probability assumptions or finite activity.
-- source:
--   Source-free measure-theoretic bridge to b879 shift child: restrict the marked measures to the two half-open windows, push them to the ℝ mark coordinate, prove the resulting measures equal by Measure.ext on all measurable B, then apply lintegral_map. Counts may be infinite.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
    (μ ν : Measure (ℝ≥0 × ℝ)) (s T : ℝ≥0)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    (hRect : ∀ B : Set ℝ, MeasurableSet B →
      μ (Ioc 0 T ×ˢ B) = ν (Ioc s (s + T) ×ˢ B)) :
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂μ) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if s < p.1 ∧ p.1 ≤ s + T then g p.2 else 0 ∂ν) := by sorry
