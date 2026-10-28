-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_neumann_primitive_step_local_L1
-- name    : AvramDividend.Classical.causal_weighted_neumann_primitive_step_local_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:38:21.143835+00:00
-- url     : https://prove2.me/theorems/87bfc009-e61e-46c5-bd91-d7f0e57dbe54
-- title:
--   Weighted signed Neumann convolution powers satisfy a primitive recurrence
-- statement:
--   Two exponentially weighted kernels integrable on a finite time interval satisfy an exact integrated convolution identity: the weighted primitive of k*P is the convolution of the weighted k with the weighted primitive of P. This bridges damped signed Neumann powers to the undamped Gaussian derivative-resolvent equation.
-- source:
--   Apply the Proved exponential causal-convolution twist to the two weighted kernels, reverse their finite-horizon convolution, then apply the new local-local L1 triangle-Fubini identity. This yields the weighted primitive recurrence required by the explicit Gaussian C1 Neumann candidate.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_exponential_twist_Ioc_convolution
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini_two_local_L1

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_neumann_primitive_step_local_L1
    (k P : ℝ → ℝ) (w x : ℝ) (hx : 0 < x)
    (hk : IntegrableOn (fun u : ℝ => Real.exp (w * u) * k u)
      (Ioc (0 : ℝ) x) volume)
    (hP : IntegrableOn (fun u : ℝ => Real.exp (w * u) * P u)
      (Ioc (0 : ℝ) x) volume) :
    (∫ t in Ioc (0 : ℝ) x,
      Real.exp (w * t) *
        (∫ s in Ioc (0 : ℝ) t, k s * P (t - s) ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x,
      (Real.exp (w * (x - s)) * k (x - s)) *
        (∫ t in Ioc (0 : ℝ) s,
          Real.exp (w * t) * P t ∂volume) ∂volume) := by sorry
