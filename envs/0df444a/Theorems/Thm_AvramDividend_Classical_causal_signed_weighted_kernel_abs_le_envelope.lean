-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_signed_weighted_kernel_abs_le_envelope
-- name    : AvramDividend.Classical.causal_signed_weighted_kernel_abs_le_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:01:45.035979+00:00
-- url     : https://prove2.me/theorems/a0f0c306-5731-4347-8e3a-fa160bf97821
-- title:
--   Signed damped Volterra kernel is bounded by its nonnegative envelope
-- statement:
--   For positive a and a nonnegative kernel at time t, the absolute value of the signed, exponentially damped Volterra kernel is bounded by the corresponding positive envelope with |β|. This enables dominated convolution-power estimates with signed drift.
-- source:
--   Gaussian C2 derivative-resolvent Neumann series, pointwise signed-kernel domination.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set

theorem AvramDividend.Classical.causal_signed_weighted_kernel_abs_le_envelope
    (K : ℝ → ℝ) (w β a t : ℝ) (ha : 0 < a) (hK : 0 ≤ K t) :
    |a⁻¹ * Real.exp (-w * t) * (β + K t)| ≤
      a⁻¹ * Real.exp (-w * t) * (|β| + K t) := by sorry
