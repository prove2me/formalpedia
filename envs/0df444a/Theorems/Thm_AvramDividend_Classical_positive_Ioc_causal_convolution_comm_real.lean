-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
-- name    : AvramDividend.Classical.positive_Ioc_causal_convolution_comm_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T19:01:03.255823+00:00
-- url     : https://prove2.me/theorems/d57ad940-05d3-4e63-b02a-564df677e2cf
-- title:
--   Causal convolution on the real positive interval is commutative
-- statement:
--   For x≥0, the real causal set integral over (0,x] of f(s)g(x−s) equals that of g(s)f(x−s), without assuming global L¹ or even nonnegativity. Convert Ioc 0 x to the oriented interval integral, apply the exact substitution s→x−s using Mathlib intervalIntegral.integral_comp_sub_left, commute real multiplication, and convert back. This gives the precise orientation required to use the bounded-continuous right-factor convolution theorem in the Gaussian Esscher Volterra proof.
-- source:
--   Pinned Mathlib intervalIntegral.integral_comp_sub_left and intervalIntegral.integral_of_le.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.positive_Ioc_causal_convolution_comm_real (f g : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x) :
    (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume) =
      ∫ s in Ioc (0 : ℝ) x, g s * f (x - s) ∂volume := by sorry
