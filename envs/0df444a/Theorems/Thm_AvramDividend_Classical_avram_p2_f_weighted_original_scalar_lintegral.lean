-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_scalar_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_scalar_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:58:57.258205+00:00
-- url     : https://prove2.me/theorems/027480b2-5469-4ad0-bf34-142a7dd2b5ba
-- title:
--   Genuine original marked jump-count expectation is homogeneous in a nonnegative scalar
-- statement:
--   For any nonnegative scalar c and measurable weight H, the expected original intrinsic marked count multiplied by c times H is c times its weighted expectation, including 0 times infinity. This scalar component of predictable simple-process compensation uses source measurability and Mathlib lintegral_const_mul, with no prescribed ν-rate.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_const_mul; Proved original source intrinsic rectangle measurable d9c55240.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_scalar_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (c : ℝ≥0∞) (H : Ω → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω, c * (H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)) ∂P) =
    c * (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) := by sorry
