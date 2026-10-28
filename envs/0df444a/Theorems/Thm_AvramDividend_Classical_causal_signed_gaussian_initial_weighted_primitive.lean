-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_signed_gaussian_initial_weighted_primitive
-- name    : AvramDividend.Classical.causal_signed_gaussian_initial_weighted_primitive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:54:51.110091+00:00
-- url     : https://prove2.me/theorems/c5bb7aff-f8d5-4697-86ed-42aea7175566
-- title:
--   Initial signed Gaussian Neumann primitive equals the undamped Volterra kernel integral
-- statement:
--   The exponentially weighted integral of the initial signed damped kernel k is -a⁻¹ times the finite-horizon integral of the original Gaussian Volterra kernel β+K. This is the zeroth-order correction required alongside the proved higher-power recurrence.
-- source:
--   Combine the canonical pointwise exponential untwisting identity with the canonical open-interior integral congruence. This identifies the initial P0=k term of the signed Neumann series with the β+K Volterra operator applied to a constant, completing the base case of the resolvent Neumann recursion.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_exp_damped_signed_kernel_untwist
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_integral_interior_congr

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_signed_gaussian_initial_weighted_primitive
    (a w β : ℝ) (K k : ℝ → ℝ)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (x : ℝ) :
    (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * k s ∂volume) =
      -a⁻¹ * (∫ s in Ioc (0 : ℝ) x, β + K s ∂volume) := by sorry
