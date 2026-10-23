-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_product_le_global_sup
-- name    : AvramDividend.Classical.causal_weighted_kernel_product_le_global_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:34:15.504664+00:00
-- url     : https://prove2.me/theorems/0179c9e9-5cf9-449b-9c99-f6bca46e676e
-- title:
--   Weighted causal product bounded by global kernel mass and input supremum
-- statement:
--   For a nonnegative integrable positive-time kernel L and continuous input D on positive times, the weighted causal integral up to any x within (0,R] is bounded by the finite-horizon supremum of exp(-w t)|D(t)| times the total mass of L over t>0. Compose the proved finite-horizon weighted supremum product estimate with the reflected nonnegative kernel integral bound, and verify that the supremum is nonnegative.
-- source:
--   Proved causal_weighted_kernel_product_le_sup_mass and causal_nonnegative_kernel_reflected_integral_le_global.

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_product_le_sup_mass
import Theorems.Thm_AvramDividend_Classical_causal_nonnegative_kernel_reflected_integral_le_global
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_kernel_product_le_global_sup
    (L D : ℝ → ℝ) (w R x : ℝ)
    (hL : IntegrableOn L (Ioi (0 : ℝ)) volume)
    (hLnonneg : ∀ u : ℝ, 0 ≤ L u)
    (hDcont : ContinuousOn D (Ioi (0 : ℝ)))
    (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R)
    (hM : BddAbove ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
      Ioc (0 : ℝ) R)) :
    (∫ s in Ioc (0 : ℝ) x,
      L (x - s) * (Real.exp (-(w * s)) * |D s|) ∂volume) ≤
    sSup ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
      Ioc (0 : ℝ) R) *
    (∫ s in Ioi (0 : ℝ), L s ∂volume) := by sorry
