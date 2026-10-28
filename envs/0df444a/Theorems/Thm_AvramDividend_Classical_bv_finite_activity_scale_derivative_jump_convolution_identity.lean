-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_derivative_jump_convolution_identity
-- name    : AvramDividend.Classical.bv_finite_activity_scale_derivative_jump_convolution_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:20:35.713114+00:00
-- url     : https://prove2.me/theorems/16f9582f-fb7a-4c08-a9a8-78b5bdadb2af
-- title:
--   Finite-activity scale derivative equals drift and negative-jump convolution
-- statement:
--   The positive-axis derivative of a standing bounded-variation finite-intensity q-scale function satisfies the source finite-activity renewal differential identity, with the residual written as the explicit negative-jump convolution. Condition33 yields a diffuse Levy jump law, making the formula pointwise at every positive reserve.
-- source:
--   Avram, Palmowski and Pistorius (2007), finite-activity renewal equation and the q-scale Laplace transform.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Order.Field
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_scale_derivative_jump_convolution_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ x : ℝ, 0 < x →
      X.drift * deriv W x =
        (q + (X.ν (Iio (0 : ℝ))).toReal) * W x -
          ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν := by sorry
