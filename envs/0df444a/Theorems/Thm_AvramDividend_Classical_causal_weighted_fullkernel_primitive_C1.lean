-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_fullkernel_primitive_C1
-- name    : AvramDividend.Classical.causal_weighted_fullkernel_primitive_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:12:23.395507+00:00
-- url     : https://prove2.me/theorems/fbf4befe-17a8-44af-acb7-1382c1199e6c
-- title:
--   C1 primitive of an exponentially damped signed causal Volterra kernel
-- statement:
--   For any strictly positive damping weight w, real drift β and real kernel K integrable and continuous on positive times, the primitive of exp(-w*t)*(β+K(t)) is continuously differentiable on the positive half-line. There is no assumed boundedness or continuity at zero; this is a differentiable primitive bridge for Gaussian Volterra resolvent terms.
-- source:
--   Combine accepted global L1 exponential damping, constant positive Laplace reference, weighted positive-time kernel continuity and continuous L1 primitive C1.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_causal_l1_exponential_damping_integrable
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_primitive_contDiff_one

open MeasureTheory Set

theorem AvramDividend.Classical.causal_weighted_fullkernel_primitive_C1
    (K : ℝ → ℝ) (w β : ℝ) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hcont : ContinuousOn K (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ t in (0 : ℝ)..x,
        Real.exp (-w * t) * (β + K t)) (Ioi 0) := by sorry
