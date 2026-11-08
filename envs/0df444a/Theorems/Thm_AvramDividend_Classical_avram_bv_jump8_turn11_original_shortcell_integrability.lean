-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_original_shortcell_integrability
-- name    : AvramDividend.Classical.avram_bv_jump8_turn11_original_shortcell_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:23:39.671369+00:00
-- url     : https://prove2.me/theorems/40c4245f-5f0b-453e-9c8a-d22e50306300
-- title:
--   Original-X short-cell marked product and marked loss are Bochner integrable
-- statement:
--   For the literal original-X strictly negative marked jumps on (0,1/(n+1)], prove real Bochner integrability of the finite exponential product and of the sum of exponential losses. Use exact original source count measurability and finite cutoff moment, without an external arbitrary Poisson random measure.
-- source:
--   For the literal original-X strictly negative marked jumps on (0,1/(n+1)], prove real Bochner integrability of the finite exponential product and of the sum of exponential losses. Use exact original source count measurability and finite cutoff moment, without an external arbitrary Poisson random measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn11_original_shortcell_integrability
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
    Integrable W P ∧ Integrable L P := by sorry
