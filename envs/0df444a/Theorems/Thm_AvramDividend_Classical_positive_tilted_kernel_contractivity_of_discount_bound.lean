-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_tilted_kernel_contractivity_of_discount_bound
-- name    : AvramDividend.Classical.positive_tilted_kernel_contractivity_of_discount_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:47:00.098215+00:00
-- url     : https://prove2.me/theorems/d7dcb6b6-5326-429c-a625-41b50e287750
-- title:
--   Shift a discounted positive-jump bound into tilted-kernel contractivity
-- statement:
--   Let δ,q,t be positive and suppose q/t plus the positive jump compensator transform at discount t is strictly below δ. Put a=q/δ and s=t-a. Then s is positive, and after changing the denominator from t to s the shifted compensator transform at s+a=t is still strictly below δ. This converts the accepted bounded-variation renewal discount bound into contractivity of the tilted kernel.
-- source:
--   Pure positive real/ENNReal rescaling of the discounted renewal bound using positivity, ENNReal.ofReal division, lintegral constant multiplication and δ(t-q/δ)=δt-q. This bridges bv_renewal_kernel_contractivity_of_standing to the tilted-kernel transform.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- A strict discounted compensator bound at t becomes strict contractivity of the shifted positive tilted kernel at s=t-q/δ. -/
theorem positive_tilted_kernel_contractivity_of_discount_bound
    (μ : Measure ℝ≥0) (δ q t : ℝ)
    (hδ : 0 < δ) (hq : 0 < q) (ht : 0 < t)
    (hsmall :
      ENNReal.ofReal (q / t) +
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal
            ((1 - Real.exp (-t * (z : ℝ))) / t) ∂μ) <
        ENNReal.ofReal δ) :
    let a : ℝ := q / δ
    let s : ℝ := t - a
    0 < s ∧
      (∫⁻ z : ℝ≥0,
        ENNReal.ofReal
          ((1 - Real.exp (-(s + a) * (z : ℝ))) / s) ∂μ) <
        ENNReal.ofReal δ := by
  sorry

end AvramDividend.Classical
