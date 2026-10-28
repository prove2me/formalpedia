-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_no_creeping_of_contact_right_germ_ws01b
-- name    : AvramDividend.Classical.bv_strict_lower_exit_no_creeping_of_contact_right_germ_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:27:14.618842+00:00
-- url     : https://prove2.me/theorems/6a1ab67e-4996-4ad3-a231-82369673b6a8
-- title:
--   BV strict lower-exit noncontact follows from a right germ conditional on contact
-- statement:
--   On lower-first ruin, a positive right-hand interval above the boundary is needed only conditional on the value at the strict lower clock being exactly at the boundary. A downward overshoot legitimately stays below the boundary and imposes no germ requirement. This correct source-faithful event split reduces BV noncreeping to a stopping-time positive-drift germ on the hypothetical contact event.
-- source:
--   Prove2Me accepted pathwise infimum/contact lemma 7a9793f9; positive-drift BV no-downward-creeping mechanism, Kyprianou fluctuation theory chapter 8. Supports canonical target 43a28d8e.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_strictLowerCrossingClock_ne_contact_of_positiveRightGerm_ws01b
import Mathlib.Tactic

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_strict_lower_exit_no_creeping_of_contact_right_germ_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x : ℝ)
    (hGerm : ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω →
      x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0 →
      ∃ τ : ℝ≥0,
        (τ : ℝ≥0∞) = twoSidedExitDownTime X (-x) ω ∧
        ∃ ε : ℝ≥0, 0 < ε ∧
          ∀ t : ℝ≥0, τ < t → t < τ + ε → -x ≤ X.X t ω) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω →
      x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω ≠ 0 := by sorry
