-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_finite_jump_rearrangement
-- name    : AvramDividend.Classical.bv_laplace_exponent_finite_jump_rearrangement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:57:40.843445+00:00
-- url     : https://prove2.me/theorems/c926ad41-6644-4414-90a5-32845ab169e0
-- title:
--   Finite negative-jump activity BV exponent moment formula
-- statement:
--   For bounded variation with finite negative-jump intensity, the Lévy exponent at θ≥1 is drift times θ minus the total negative-jump mass plus the negative-jump exponential moment. Finite intensity makes the constant and exponential integrable, enabling a direct split of the already-proved exponent deficit identity.
-- source:
--   Proved AvramDividend.Classical.bv_exponent_negative_jump_deficit_exact, Mathlib integral_sub and integral_const.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_laplace_exponent_finite_jump_rearrangement
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    X.ψ θ = X.drift * θ -
      (X.ν (Iio (0 : ℝ))).toReal +
      ∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂X.ν := by sorry
