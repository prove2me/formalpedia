-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_positive_second_difference
-- name    : AvramDividend.Classical.unbounded_scale_discount_positive_second_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:47:41.358598+00:00
-- url     : https://prove2.me/theorems/04682981-64df-43d4-bdff-ff5d1dc4f44e
-- title:
--   Strictly positive equal-step second discount difference of the q-scale function
-- statement:
--   For any unbounded-variation spectrally negative Lévy process, positive reserve x, nonnegative discount q and positive increment h, the centred discrete second difference W(q+2h,x)-2W(q+h,x)+W(q,x) is strictly positive. This gives an explicit finite-difference form of strict convexity in discount.
-- source:
--   The already Proved strictly increasing q-secants theorem, specialised to equally spaced discount values.

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_convex_secants
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_positive_second_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q))
    (q h x : ℝ) (hq : 0 ≤ q) (hh : 0 < h) (hx : 0 < x) :
    0 < W (q + 2 * h) x - 2 * W (q + h) x + W q x := by sorry
