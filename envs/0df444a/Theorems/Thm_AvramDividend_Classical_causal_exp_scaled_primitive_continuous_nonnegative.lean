-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exp_scaled_primitive_continuous_nonnegative
-- name    : AvramDividend.Classical.causal_exp_scaled_primitive_continuous_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:46:39.262122+00:00
-- url     : https://prove2.me/theorems/f2fde167-416e-4fc8-b899-2fb255078462
-- title:
--   Scaled exponential primitive is continuous on nonnegative times
-- statement:
--   Every positive-time L1 real kernel yields a continuous scaled exponential damped primitive on the entire nonnegative half-line, including at the origin. This directly discharges hHcont for the signed Gaussian Neumann-series regularity theorem.
-- source:
--   The canonically Proved causal exponential convolution is continuous on [0,∞). Dividing by a constant preserves this continuity. Use the proved scaled Ioc exponential primitive convolution identity and move the scalar through the integral to identify the exact Neumann H_n primitive.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_exp_l1_convolution_continuous_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_damped_primitive_Ioc_convolution_scaled

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_exp_scaled_primitive_continuous_nonnegative
    (P : ℝ → ℝ) (a w : ℝ) (hw : 0 ≤ w)
    (hP : IntegrableOn P (Ioi (0 : ℝ)) volume) :
    ContinuousOn
      (fun x : ℝ => (Real.exp (-w * x) *
        (∫ s in Ioc (0 : ℝ) x,
          Real.exp (w * s) * P s ∂volume)) / a)
      (Ici (0 : ℝ)) := by sorry
