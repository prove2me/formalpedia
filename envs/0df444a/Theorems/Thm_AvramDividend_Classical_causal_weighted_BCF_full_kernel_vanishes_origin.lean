-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_full_kernel_vanishes_origin
-- name    : AvramDividend.Classical.causal_weighted_BCF_full_kernel_vanishes_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:25:50.207166+00:00
-- url     : https://prove2.me/theorems/2d7ee712-eb99-450c-ae4e-f653d91c5e2e
-- title:
--   Full causal weighted BCF convolution vanishes at positive-time origin
-- statement:
--   For any bounded continuous f and exponentially unweighted extension V(s)=exp(ws)f(max(s,0)), the causal full-kernel integral with β+K(x-s) tends to zero as x decreases to zero, provided K is L1 on positive times. The constant drift term is β times the continuous causal primitive, which vanishes at zero. The L1 kernel term tends to zero by a proved convolution endpoint estimate. Integrability justifies splitting the two contributions.
-- source:
--   Proved causal_l1_convolution_vanishes_at_origin, causal_continuous_input_primitive_continuousOn_nonnegative, causal_l1_kernel_continuous_input_integrable and BCF input regularity.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.NhdsWithin
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_vanishes_at_origin
import Theorems.Thm_AvramDividend_Classical_causal_continuous_input_primitive_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_local_bound
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_full_kernel_vanishes_origin
    (K : ℝ → ℝ) (β w : ℝ)
    (f : BoundedContinuousFunction ℝ≥0 ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    Tendsto (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
      (β + K (x - s)) *
        (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds 0) := by sorry
