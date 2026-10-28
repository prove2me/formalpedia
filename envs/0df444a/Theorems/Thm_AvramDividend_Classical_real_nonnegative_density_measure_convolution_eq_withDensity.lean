-- Prove2me | Theorems.Thm_AvramDividend_Classical_real_nonnegative_density_measure_convolution_eq_withDensity
-- name    : AvramDividend.Classical.real_nonnegative_density_measure_convolution_eq_withDensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:19:28.953697+00:00
-- url     : https://prove2.me/theorems/1e905f7a-e894-49fc-bfb1-8270edf1cfc9
-- title:
--   Measure convolution of nonnegative real densities equals measure of their real convolution
-- statement:
--   For nonnegative measurable real functions κ and f with absolutely integrable real convolution at each x, the convolution of their Lebesgue withDensity measures is the Lebesgue withDensity measure whose density is the ordinary real convolution. Combines pinned Mathlib conv_withDensity_eq_lconvolution and the separately remotely elaborated pointwise ENNReal-to-real lconvolution bridge. This identifies the measure convolution powers in the finite BV Esscher geometric renewal measure with the real convolution powers in causal_subunit_renewal_full_real_power_package, advancing scale identification 1ca4a724.
-- source:
--   Pinned Mathlib conv_withDensity_eq_lconvolution; canonical nonnegative_real_convolution_lconvolution_ofReal_bridge.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_convolution_lconvolution_ofReal_bridge
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.real_nonnegative_density_measure_convolution_eq_withDensity
    (κ f : ℝ → ℝ)
    (hκpos : ∀ y : ℝ, 0 ≤ κ y) (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (hκmeas : Measurable κ) (hfmeas : Measurable f)
    (hconv : ∀ x : ℝ,
      Integrable (fun y : ℝ => κ y * f (x - y)) volume) :
    (volume.withDensity (fun y : ℝ => ENNReal.ofReal (κ y))).conv
      (volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))) =
    volume.withDensity (fun x : ℝ =>
      ENNReal.ofReal (∫ y : ℝ, κ y * f (x - y) ∂volume)) := by sorry
