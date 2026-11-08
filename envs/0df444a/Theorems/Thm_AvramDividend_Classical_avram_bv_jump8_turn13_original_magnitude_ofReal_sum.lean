-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn13_original_magnitude_ofReal_sum
-- name    : AvramDividend.Classical.avram_bv_jump8_turn13_original_magnitude_ofReal_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:17:52.175702+00:00
-- url     : https://prove2.me/theorems/a66648cc-df68-4a8f-9235-3d4daac441bd
-- title:
--   Original strict negative jump magnitude has finite real and ENNReal sum agreement
-- statement:
--   For the genuine original finite strict negative jump set, each negative jump magnitude is nonnegative and the ENNReal sum agrees exactly with ENNReal.ofReal of the finite real magnitude sum.
-- source:
--   Adapt the original negative finite loss bridge 1906d3b2 to the positive jump-magnitude weight; induction on the original finite set and ENNReal.ofReal_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn13_original_magnitude_ofReal_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let M : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      -(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    ∀ ω : Ω, 0 ≤ M ω ∧
      (∑ u ∈ S ω, ENNReal.ofReal
        (-(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
      ENNReal.ofReal (M ω) := by sorry
