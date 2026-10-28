-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_volterra_integral_identity
-- name    : AvramDividend.Classical.bv_finite_activity_scale_volterra_integral_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:32:21.328001+00:00
-- url     : https://prove2.me/theorems/a4f7247a-3493-4ed0-a8df-a712914821f1
-- title:
--   Finite-activity scale transform yields its integrated drift and jump renewal equation
-- statement:
--   The original q-scale Laplace equation, together with the compound-Poisson-plus-positive-drift Lévy exponent under finite negative-jump activity, yields an integrated Volterra renewal identity on the positive real axis. The lower-limit term is the positive-drift initial atom, and the negative-jump contribution is the integrated convolution.
-- source:
--   Avram, Palmowski and Pistorius (2007), scale transform and BV renewal equation.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_scale_volterra_integral_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ x : ℝ, 0 < x →
      X.drift * W x =
        1 + (q + (X.ν (Iio (0 : ℝ))).toReal) *
          (∫ z in (0 : ℝ)..x, W z) -
          ∫ z in (0 : ℝ)..x,
            (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν) := by sorry
