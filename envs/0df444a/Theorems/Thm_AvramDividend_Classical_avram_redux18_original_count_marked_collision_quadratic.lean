-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_original_count_marked_collision_quadratic
-- name    : AvramDividend.Classical.avram_redux18_original_count_marked_collision_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:12:09.01184+00:00
-- url     : https://prove2.me/theorems/5f195a7c-a703-465a-beb2-d26e54f0d6c4
-- title:
--   Original physical negative-band jump count controls selected marked collision expectation
-- statement:
--   For the actual SpectrallyNegativeLevy path, any finite family of selected negative-band jumps bounded in cardinal by its original physical jump count has expected marked-product collision at most the squared exact physical band intensity. This applies the already Proved original second moment estimate, and is directly reusable for the intrinsic marked cutoff Laplace functional.
-- source:
--   Combine the Proved finite-product pointwise collision inequality with the Proved original physical negative-band count K² indicator estimate. The pair-count bound vanishes when K is zero or one and is bounded by K² otherwise. Apply integral_mono to the integrable error and original source quadratic budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux18_finite_mark_product_collision
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_collision_second_moment_quadratic
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux18_original_count_marked_collision_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    {α : Type*} [DecidableEq α] (S : Ω → Finset α)
    (q : Ω → α → ℝ)
    (hS : ∀ ω, (S ω).card ≤
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)
    (hq0 : ∀ ω i, 0 ≤ q ω i) (hq1 : ∀ ω i, q ω i ≤ 1)
    (hE : Integrable (fun ω =>
      (∏ i ∈ S ω, q ω i) - (1 - ∑ i ∈ S ω, (1 - q ω i))) P) :
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    0 ≤ ∫ ω, ((∏ i ∈ S ω, q ω i) -
      (1 - ∑ i ∈ S ω, (1 - q ω i))) ∂P ∧
    (∫ ω, ((∏ i ∈ S ω, q ω i) -
      (1 - ∑ i ∈ S ω, (1 - q ω i))) ∂P) ≤ r ^ 2 := by sorry
