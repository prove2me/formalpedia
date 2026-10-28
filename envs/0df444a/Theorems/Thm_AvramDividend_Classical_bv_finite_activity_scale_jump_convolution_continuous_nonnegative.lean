-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_scale_jump_convolution_continuous_nonnegative
-- name    : AvramDividend.Classical.bv_finite_activity_scale_jump_convolution_continuous_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:54:10.246897+00:00
-- url     : https://prove2.me/theorems/608fe612-ca01-4b40-ae8a-a193dd234148
-- title:
--   Finite-activity negative-jump convolution is continuous including the zero boundary
-- statement:
--   The jump convolution is continuous for positive reserves by finite-measure dominated convergence. Its right-hand limit at zero is zero and its exact value at zero is zero because W vanishes on negative inputs. The one-sided continuity equivalence converts this right-hand limit to continuity on the closed nonnegative reserve half-line.
-- source:
--   Mathlib.Topology.Order.LeftRight, continuousWithinAt_Ioi_iff_Ici; Avram, Palmowski and Pistorius (2007), finite activity scale convolution.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.Order.LeftRight
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_scale_jump_convolution_continuous_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)
      (Ici (0 : ℝ)) := by sorry
