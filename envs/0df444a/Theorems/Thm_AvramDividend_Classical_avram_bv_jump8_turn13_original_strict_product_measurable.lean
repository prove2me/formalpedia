-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn13_original_strict_product_measurable
-- name    : AvramDividend.Classical.avram_bv_jump8_turn13_original_strict_product_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:08:13.414946+00:00
-- url     : https://prove2.me/theorems/73b1b981-5226-47ce-8795-6be165d51279
-- title:
--   Original strict negative finite exponential product is source-measurable
-- statement:
--   On every genuine Levy sample path, the finite strict negative marked exponential product on (0,1/(n+1)] is a measurable real random variable.
-- source:
--   Use Proved b50e56f2 for a negative-mark magnitude intrinsic weighted path extension, Proved 35828b50 for original finite sum of marks, and finite exp-product algebra; compose with original adapted coordinate-path measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn13_original_strict_product_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    Measurable W := by sorry
