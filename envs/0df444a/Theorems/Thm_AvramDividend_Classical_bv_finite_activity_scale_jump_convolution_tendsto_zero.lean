-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_tendsto_zero
-- name    : AvramDividend.Classical.bv_finite_activity_scale_jump_convolution_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:19:55.264464+00:00
-- url     : https://prove2.me/theorems/b89dee14-a12b-4d69-bcab-a97998c638a4
-- title:
--   Finite negative-jump scale convolution vanishes at the origin
-- statement:
--   The explicit negative-jump convolution of the scale function tends to zero at the origin because W vanishes below zero, is continuous and monotone on the nonnegative axis, and the finite diffuse negative-jump Levy measure assigns vanishing mass to shrinking intervals before zero.
-- source:
--   Finite-activity Volterra boundary limit from Avram, Palmowski and Pistorius (2007).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Order.Field
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_scale_jump_convolution_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    Tendsto (fun x : ℝ =>
      ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by sorry
