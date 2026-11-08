-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_shortcell_original_marked_bochner_range
-- name    : AvramDividend.Classical.avram_bv_jump8_turn10_shortcell_original_marked_bochner_range
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:48:53.343367+00:00
-- url     : https://prove2.me/theorems/af216019-9031-4b2f-ad6c-5d376fbd3eff
-- title:
--   Original-X finite marked short-cell products and losses are integrable, and product expectation lies in [0,1]
-- statement:
--   For the actual source Lévy process original strict negative marked jump set, finite marked product and weighted loss are measurable and integrable. Every original negative jump exponential weight lies in (0,1], so its finite product and expectation are in [0,1].
-- source:
--   For the actual source Lévy process original strict negative marked jump set, finite marked product and weighted loss are measurable and integrable. Every original negative jump exponential weight lies in (0,1], so its finite product and expectation are in [0,1].

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn10_shortcell_original_marked_bochner_range
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
    Integrable W P ∧ Integrable L P ∧
    0 ≤ ∫ ω, W ω ∂P ∧ (∫ ω, W ω ∂P) ≤ 1 := by sorry
