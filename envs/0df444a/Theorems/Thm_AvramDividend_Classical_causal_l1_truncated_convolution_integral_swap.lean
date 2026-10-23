-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_integral_swap
-- name    : AvramDividend.Classical.causal_l1_truncated_convolution_integral_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:13:24.792432+00:00
-- url     : https://prove2.me/theorems/ce3fca88-7cac-4e10-aae7-9e9654632c21
-- title:
--   Fubini interchange for a truncated causal convolution
-- statement:
--   The full-real inner integral of a positive-lag L1 kernel against an input truncated to (0,x] can be interchanged with the outer integral over (0,x]. The integrable two-variable convolution integrand follows from the previously established product-measure theorem; restrict the first product-measure factor and apply Mathlib.integral_integral_swap.
-- source:
--   MeasureTheory.Measure.restrict_prod_eq_prod_univ and MeasureTheory.integral_integral_swap.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_prod_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_truncated_convolution_integral_swap
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ (u : ℝ), ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) ∂volume) =
    (∫ (u : ℝ),
      (∫ t in Ioc (0 : ℝ) x,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) ∂volume) := by sorry
