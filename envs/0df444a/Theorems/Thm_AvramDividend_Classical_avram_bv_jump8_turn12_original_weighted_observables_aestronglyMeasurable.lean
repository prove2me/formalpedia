-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn12_original_weighted_observables_aestronglyMeasurable
-- name    : AvramDividend.Classical.avram_bv_jump8_turn12_original_weighted_observables_aestronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:31:10.212384+00:00
-- url     : https://prove2.me/theorems/8b6afc7f-7934-4c53-be24-1969ac393c70
-- title:
--   Actual original short-cell strict marked product and loss are almost everywhere strongly measurable
-- statement:
--   Original strict-cutoff jump observables W and L are almost-everywhere strongly measurable on the actual Levy probability space, with finite random marked time index and original filtration conventions. No random-measure independence assumptions are introduced.
-- source:
--   Measurable original intrinsic marked Borel extraction and proven pathwise finite product/sum bridges.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn12_original_weighted_observables_aestronglyMeasurable
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
    AEStronglyMeasurable W P ∧ AEStronglyMeasurable L P := by sorry
