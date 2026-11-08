-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_shortcell_original_marked_collision_expectation
-- name    : AvramDividend.Classical.avram_bv_jump8_turn10_shortcell_original_marked_collision_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:49:03.710485+00:00
-- url     : https://prove2.me/theorems/9a89f55b-a2ba-455c-9041-3d2e25e82b75
-- title:
--   Original-X marked finite-product collision expectation is nonnegative and quadratic
-- statement:
--   Specialise the Proved original marked product-collision second moment 5f195a7c using the strict-to-closed mark-count cardinal bound b34d2b11 and original negative-jump exponential weights. Obtain the exact real expectation collision in a short cell bounded by T² times ν(Iic(-δ))², including integrability needed for the Bochner integral.
-- source:
--   Specialise the Proved original marked product-collision second moment 5f195a7c using the strict-to-closed mark-count cardinal bound b34d2b11 and original negative-jump exponential weights. Obtain the exact real expectation collision in a short cell bounded by T² times ν(Iic(-δ))², including integrability needed for the Bochner integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn10_shortcell_original_marked_collision_expectation
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
    0 ≤ ∫ ω, (W ω - (1 - L ω)) ∂P ∧
    (∫ ω, (W ω - (1 - L ω)) ∂P) ≤
      (1 / ((n : ℝ) + 1)) ^ 2 *
      ((X.ν (Iic (-(1 / ((k : ℝ) + 1))))).toReal) ^ 2 := by sorry
