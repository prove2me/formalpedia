-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_residual_nonnegative_weight_negative_budget
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_residual_nonnegative_weight_negative_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:45:12.303605+00:00
-- url     : https://prove2.me/theorems/3aa86a9d-790b-45e5-827b-514c1c7efccb
-- title:
--   Original BV residual continuous finite Stieltjes mass contributes a nonpositive signed derivative budget
-- statement:
--   For the original bounded-variation spectrally negative Levy process there is almost surely an atomless locally finite Stieltjes measure for the true physical-drift-minus-actual-jumps residual, and integrating any everywhere nonnegative derivative weight against that residual measure contributes a nonpositive signed correction. This allows the upper BV verification estimate to discard the residual term when the stopped derivative weight is nonnegative, even before proving that the residual vanishes.
-- source:
--   Uses accepted original locally finite atomless residual theorem 4f9a8a4a, pinned measure integral nonnegativity, and neg_nonpos. The signed measure contribution reflects X = physical_drift_time minus actual negative jumps minus the continuous nondecreasing residual, all on the same original source.

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_residual_nonnegative_weight_negative_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      (∀ a b : ℝ≥0, a ≤ b →
        μ (Ioc a b) = ENNReal.ofReal (
          ((((b : ℝ) * X.drift - X.X b ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
          (((a : ℝ) * X.drift - X.X a ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))))) ∧
      (∀ a : ℝ≥0, μ {a} = 0) ∧
      (∀ a b : ℝ≥0, a ≤ b → μ (Ioc a b) < ∞) ∧
      (∀ g : ℝ≥0 → ℝ, (∀ t, 0 ≤ g t) →
        -(∫ t, g t ∂μ) ≤ 0) := by sorry
