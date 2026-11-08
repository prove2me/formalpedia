-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_original_shortcell_product_pointwise_bounds
-- name    : AvramDividend.Classical.avram_bv_jump8_turn11_original_shortcell_product_pointwise_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:23:35.784047+00:00
-- url     : https://prove2.me/theorems/3c140436-6361-451c-ba4d-193a1b799d10
-- title:
--   Original-X finite strict negative exponential jump product lies pointwise in [0,1]
-- statement:
--   Each literal original strict negative jump on (0,1/(n+1)] has real exponential mark weight in (0,1]. Their finite product is pointwise between 0 and 1, including the empty mark set and zero clock.
-- source:
--   Each literal original strict negative jump on (0,1/(n+1)] has real exponential mark weight in (0,1]. Their finite product is pointwise between 0 and 1, including the empty mark set and zero clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn11_original_shortcell_product_pointwise_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    ∀ ω : Ω, 0 ≤ W ω ∧ W ω ≤ 1 := by sorry
