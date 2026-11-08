-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux21_original_strict_mark_product_remainder
-- name    : AvramDividend.Classical.avram_redux21_original_strict_mark_product_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:59:28.57019+00:00
-- url     : https://prove2.me/theorems/82001b03-b2c9-499c-8e94-1bc335676ff0
-- title:
--   Original finite strict negative Lévy jumps satisfy quadratic product-remainder bound
-- statement:
--   For actual original negative Lévy jumps on an arbitrary bounded physical time interval, the exponential-product remainder is nonnegative and at most half the second factorial count of original strict marked jump times.
-- source:
--   The literal strict negative cutoff finite jump-time set has nonpositive jump marks. Apply the already proved arbitrary finite marked-product remainder to the original exponential factors, without assuming a hypothetical auxiliary Poisson random measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux20_finite_mark_product_first_order_remainder
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux21_original_strict_mark_product_remainder
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let S : Finset ℝ≥0 :=
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let z : ℝ≥0 → ℝ := fun u =>
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    0 ≤ (∏ u ∈ S, z u) - (1 - ∑ u ∈ S, (1 - z u)) ∧
    2 * ((∏ u ∈ S, z u) - (1 - ∑ u ∈ S, (1 - z u))) ≤
      (S.card : ℝ) * ((S.card : ℝ) - 1) := by sorry
