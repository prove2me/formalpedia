-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_volterra_laplace_family
-- name    : AvramDividend.Classical.bv_finite_activity_volterra_laplace_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:31:21.821197+00:00
-- url     : https://prove2.me/theorems/a8b80498-97ec-43f7-806b-e09eaa606725
-- title:
--   Full Laplace family for finite-activity scale Volterra renewal
-- statement:
--   For sufficiently large Laplace parameters, both sides of the finite-activity integrated scale renewal equation have exponentially integrable restrictions to positive reserves and their Laplace transforms are equal. Combine the q-scale and jump-convolution transforms, exponential integrability of interval primitives, bounded-variation exponent rearrangement and the scalar transform identity.
-- source:
--   Finite-activity scale and Levy jump-convolution Laplace transforms, cumulative integral formula, BV exponent algebra, and eventual exponent growth.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_volterra_laplace_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * X.drift * W x)
        (Ioi (0 : ℝ)) volume ∧
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
          (∫ z in (0 : ℝ)..x, W z) -
        ∫ z in (0 : ℝ)..x,
          (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν)))
        (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * X.drift * W x) =
      ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
          (∫ z in (0 : ℝ)..x, W z) -
        ∫ z in (0 : ℝ)..x,
          (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν)) := by sorry
