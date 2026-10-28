-- Prove2me | Theorems.Thm_AvramDividend_Classical_withDensity_injective_of_everywhere_pos_finite
-- name    : AvramDividend.Classical.withDensity_injective_of_everywhere_pos_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:44:37.389927+00:00
-- url     : https://prove2.me/theorems/642d4c3e-d630-414a-8eac-972aa3b4ca58
-- title:
--   Injectivity of weighting a measure by an everywhere positive finite density
-- statement:
--   Let μ and ν be two measures on the same measurable space, and let f be a measurable extended-nonnegative density that is strictly positive and finite everywhere. If the weighted measures μ.withDensity f and ν.withDensity f agree, then the original measures agree. The proof applies Mathlib's inverse-weighting identity independently to each measure and cancels the common positive density. This is the exact de-tilting step needed in the positive one-sided Laplace/MGF uniqueness argument used to identify a canonical Lévy model's one-time distributions.
-- source:
--   Mathlib.MeasureTheory.Measure.WithDensity: withDensity_inv_same, ae_of_all. No stochastic prerequisites. Useful for positive-MGF law uniqueness [4fb183cd-2d4f-4df5-8a23-9c6e5b201da0].

import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.withDensity_injective_of_everywhere_pos_finite
    {α : Type} [MeasurableSpace α]
    (μ ν : Measure α) (f : α → ℝ≥0∞)
    (hf : Measurable f)
    (hpos : ∀ x, f x ≠ 0)
    (hfinite : ∀ x, f x ≠ ⊤)
    (heq : μ.withDensity f = ν.withDensity f) : μ = ν := by sorry
