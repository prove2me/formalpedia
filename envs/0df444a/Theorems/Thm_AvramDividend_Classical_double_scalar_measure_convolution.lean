-- Prove2me | Theorems.Thm_AvramDividend_Classical_double_scalar_measure_convolution
-- name    : AvramDividend.Classical.double_scalar_measure_convolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:23:49.708982+00:00
-- url     : https://prove2.me/theorems/80153e49-9cb2-4a0e-83a0-f70106e37a0f
-- title:
--   Two geometric scalar weights factor through convolution of measures
-- statement:
--   For s-finite Borel measures μ and ν on the real additive group, multiplying each measure by arbitrary nonnegative extended-real scalars a and b before convolving yields the product a*b times their unscaled convolution. The measure scaling identity transfers geometric Esscher coefficients through the convolution-power recursion. Its parent application proves c^(n+1) • m(n+1) = (c•κ).conv(c^n•m n), enabling the existing canonical real convolution-power density identification to apply to the finite Esscher renewal witness.
-- source:
--   Pinned Mathlib Measure.conv_smul_left and Measure.conv_smul_right, with smul_smul.

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.WithDensity
open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.double_scalar_measure_convolution
    (a b : ℝ≥0∞) (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    (a • μ).conv (b • ν) = (a * b) • (μ.conv ν) := by sorry
