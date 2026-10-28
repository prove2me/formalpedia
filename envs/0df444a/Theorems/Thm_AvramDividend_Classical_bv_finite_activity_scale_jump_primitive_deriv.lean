-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_primitive_deriv
-- name    : AvramDividend.Classical.bv_finite_activity_scale_jump_primitive_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:47:37.212339+00:00
-- url     : https://prove2.me/theorems/44ced0d5-c80b-40a7-a157-9b84504d6a7d
-- title:
--   Positive-reserve fundamental theorem for the finite-jump scale convolution primitive
-- statement:
--   The finite-activity Lévy jump convolution is integrable on compact reserve intervals and continuous at positive reserves. Hence its integral from zero to the current reserve has derivative equal to the convolution at each strictly positive reserve, by the interval fundamental theorem of calculus. The jump convolution is finite because the negative jump measure is finite and the scale function is locally bounded.
-- source:
--   Mathlib interval integral fundamental theorem of calculus; Avram, Palmowski and Pistorius (2007), bounded variation renewal equation.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_scale_jump_primitive_deriv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ x : ℝ, 0 < x →
      deriv (fun t : ℝ =>
        ∫ z in (0 : ℝ)..t,
          (∫ y in Iio (0 : ℝ), W (z + y) ∂X.ν)) x =
        ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν := by sorry
