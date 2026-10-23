-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_closed_convolution_integral_swap
-- name    : AvramDividend.Classical.causal_l1_closed_convolution_integral_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:52:05.690683+00:00
-- url     : https://prove2.me/theorems/c82a3588-108e-4dff-a868-e7bf05781e94
-- title:
--   Interchanging a causal convolution and a finite outer-time integral
-- statement:
--   Under global product integrability of the extended positive-time kernel and input supported in the closed interval [0,x], swap the u and t integrals for t∈(0,x]. The proof restricts the product measure and invokes Bochner Fubini.
-- source:
--   Mathlib.MeasureTheory.Integral.Prod, integral_integral_swap; Mathlib.MeasureTheory.Measure.Prod, Measure.restrict_prod_eq_prod_univ.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_closed_convolution_prod_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_closed_convolution_integral_swap
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ (u : ℝ), ((Ioi (0 : ℝ)).indicator K) u *
        ((Icc (0 : ℝ) x).indicator g) (t - u) ∂volume) ∂volume) =
    (∫ (u : ℝ),
      (∫ t in Ioc (0 : ℝ) x,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Icc (0 : ℝ) x).indicator g) (t - u) ∂volume) ∂volume) := by sorry
