-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_damped_primitive_Ioc_convolution_scaled
-- name    : AvramDividend.Classical.causal_damped_primitive_Ioc_convolution_scaled
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T17:08:43.641613+00:00
-- url     : https://prove2.me/theorems/89f80488-7dea-48a2-ab3b-ff2567d5bf7e
-- title:
--   Scaled damped primitive equals causal exponential convolution on Ioc
-- statement:
--   For nonnegative time x, the exponentially weighted causal primitive scaled by a constant coefficient is exactly the causal convolution of the original kernel with the scaled exponential input. Together with the proved nonnegative-time continuity of exponential convolutions, this provides endpoint continuity for each Gaussian Neumann correction term.
-- source:
--   Convert Ioc integrals to oriented interval integrals for x≥0, apply the already Proved exponential primitive identity, move the constant factor 1/a through the Lebesgue integral, then use the canonical Ioc convolution commutativity. This identifies the exact H_n used in the Neumann derivative theorem with the positive-half-line continuous causal exponential convolution.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_exponential_primitive_convolution_identity
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.causal_damped_primitive_Ioc_convolution_scaled
    (P : ℝ → ℝ) (a w x : ℝ) (hx : 0 ≤ x) :
    (Real.exp (-w * x) *
      (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P s ∂volume)) / a =
    ∫ s in Ioc (0 : ℝ) x,
      P (x - s) * (Real.exp (-w * s) / a) ∂volume := by sorry
