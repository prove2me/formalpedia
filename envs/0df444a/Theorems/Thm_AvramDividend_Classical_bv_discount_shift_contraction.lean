-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_discount_shift_contraction
-- name    : AvramDividend.Classical.bv_discount_shift_contraction
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T10:12:06.441233+00:00
-- url     : https://prove2.me/theorems/0577b9b0-670a-495d-b5fe-7dadf92162b4
-- title:
--   Convert positive drift discount bound to strictly contractive shifted renewal Laplace mass
-- statement:
--   Given δ>0, q>0, t>0, a nonnegative jump Laplace term L(t) and the small-kernel bound q/t + L(t)/t < δ, the shifted discount s=t−q/δ is strictly positive and L(s+q/δ)<δs. This isolates the crucial real-algebra step in the tilted bounded-variation renewal construction, using only a nonnegative L(t) and no unproved stochastic assumption.
-- source:
--   Independent scalar adapter for the canonical accepted BV discounted-renewal contractivity theorem and the tilted kernel Laplace construction

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_discount_shift_contraction (L : ℝ → ℝ) (δ q t : ℝ)
    (hδ : 0 < δ) (hq : 0 < q) (ht : 0 < t)
    (hL : 0 ≤ L t)
    (hsmall : q / t + L t / t < δ) :
    0 < t - q / δ ∧
      L ((t - q / δ) + q / δ) < δ * (t - q / δ) := by
  sorry
