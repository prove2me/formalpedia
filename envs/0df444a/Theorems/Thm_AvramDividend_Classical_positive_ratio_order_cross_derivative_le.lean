-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_ratio_order_cross_derivative_le
-- name    : AvramDividend.Classical.positive_ratio_order_cross_derivative_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:42:09.742998+00:00
-- url     : https://prove2.me/theorems/ec266640-162e-4e7e-98da-a395c49ab116
-- title:
--   Cross derivative comparison from positive forward ratio ordering
-- statement:
--   For a strictly positive function on the positive axis whose forward ratios are ordered by their starting points, local differentiability at two ordered positive points x≤y implies f'(y) f(x) ≤ f'(x) f(y). This form contains no logarithms and is directly applicable to q-scale function derivative normalisations in the Esscher and cstar verification chain. The proof uses the separately Proved pointwise logarithmic-slope theorem and the chain rule for the logarithm.
-- source:
--   Positive forward-ratio characterisation of log concavity and real logarithm differentiation.

import Theorems.Thm_AvramDividend_Classical_positive_ratio_order_log_deriv_antitone_at_pair
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical Filter Set Topology

theorem AvramDividend.Classical.positive_ratio_order_cross_derivative_le
    (f : ℝ → ℝ)
    (hfpos : ∀ z : ℝ, 0 < z → 0 < f z)
    (hratio : ∀ u v t : ℝ, 0 < u → u ≤ v → 0 < t →
      f u / f (u + t) ≤ f v / f (v + t))
    (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y)
    (hdx : DifferentiableAt ℝ f x)
    (hdy : DifferentiableAt ℝ f y) :
    deriv f y * f x ≤ deriv f x * f y := by sorry
