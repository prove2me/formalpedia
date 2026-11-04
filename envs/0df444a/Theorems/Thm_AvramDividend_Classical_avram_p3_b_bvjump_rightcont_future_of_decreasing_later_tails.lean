-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_rightcont_future_of_decreasing_later_tails
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_rightcont_future_of_decreasing_later_tails
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:21:44.682819+00:00
-- url     : https://prove2.me/theorems/f22fccde-a2d8-48f7-b397-275a7e19c93f
-- title:
--   Conditional right-continuous future-cylinder intensity follows from decreasing later predictable tails
-- statement:
--   For original right-continuous predictable marked measures, equality on all strict-future cylinders after a decreasing countable cofinal sequence r_n>i implies equality on the exact strict-future cylinder after i. The source past-event measurability at r_n is explicit; it follows from right-continuous past measurability at i by filtration monotonicity. The proof uses genuine continuity of measure from below and remains valid for infinite and zero masses. This does not assume or derive the original Lévy jump rate or cell compensation.
-- source:
--   Measure continuity from below; original filtered Lévy source, Proposition 4(i), Eq. (5.13); complement to original finite adapted rectangle extension.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_rightcont_future_of_decreasing_later_tails
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (i : ℝ≥0) (A : Set Ω) (B : Set ℝ) (hB : MeasurableSet B)
    (r : ℕ → ℝ≥0) (hr : Antitone r)
    (hrAbove : ∀ n, i < r n)
    (hrCofinal : ∀ u : ℝ≥0, i < u → ∃ n, r n < u)
    (hAr : ∀ n, MeasurableSet[𝓕.rightCont (r n)] A)
    (hTail : ∀ n, M ((Ioi (r n) ×ˢ A) ×ˢ B) =
                  N ((Ioi (r n) ×ˢ A) ×ˢ B)) :
    M ((Ioi i ×ˢ A) ×ˢ B) = N ((Ioi i ×ˢ A) ×ˢ B) := by sorry
