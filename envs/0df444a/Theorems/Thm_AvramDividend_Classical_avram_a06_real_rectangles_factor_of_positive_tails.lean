-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_real_rectangles_factor_of_positive_tails
-- name    : AvramDividend.Classical.avram_a06_real_rectangles_factor_of_positive_tails
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:59:29.407743+00:00
-- url     : https://prove2.me/theorems/8f6e6140-6d65-4915-9c9b-8d3b9d133a7d
-- title:
--   All measurable residual-by-future rectangles factor from positive residual upper tails
-- statement:
--   Use positivity of R to extend tail factorisation from nonnegative to all real upper half-line thresholds. For fixed measurable future B, compare finite measures on ℝ obtained as images of the P-restricted history-and-B event and the scaled B-restricted P measure; their total masses and strict upper tails coincide. The already proved real measure uniqueness theorem supplies equality on any Borel residual set A. This is the substantive rectangle lemma required by the full product-measure extension parent.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_finite_real_measures_eq_of_Ioi
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a06_real_rectangles_factor_of_positive_tails
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hR : Measurable R)
    (F : Ω → E) (hF : Measurable F)
    (H : Set Ω) (hH : MeasurableSet H)
    (hPos : ∀ᵐ ω ∂P, 0 < R ω)
    (hTail : ∀ (u : ℝ), 0 ≤ u → ∀ (B : Set E),
      MeasurableSet B →
      P {ω | ω ∈ H ∧ u < R ω ∧ F ω ∈ B} =
        P H * P {ω | u < R ω ∧ F ω ∈ B})
    (A : Set ℝ) (hA : MeasurableSet A)
    (B : Set E) (hB : MeasurableSet B) :
    P {ω | ω ∈ H ∧ R ω ∈ A ∧ F ω ∈ B} =
      P H * P {ω | R ω ∈ A ∧ F ω ∈ B} := by sorry
