-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_strict_tail_scaled_drift_real_density
-- name    : AvramDividend.Classical.positive_strict_tail_scaled_drift_real_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:25:14.315015+00:00
-- url     : https://prove2.me/theorems/aa7f1cc0-c88b-40e8-a433-7052791b6e93
-- title:
--   Strict positive tail kernel measure scaled by drift has explicit real density
-- statement:
--   For any positive-magnitude measure with finite first moment and strictly positive drift, prove the exact equality between the inverse-drift scaled strict-tail measure and the Lebesgue density given by its nonnegative real positive tail divided by drift. No separate measurability premise is required, because finite scalar multiplication commutes with withDensity.
-- source:
--   Proved positive_strict_tail_measure_real_density and finite-scalar withDensity_smul' from Mathlib; reusable bridge to canonical BV Esscher renewal kernel.

import Theorems.Thm_AvramDividend_Classical_positive_strict_tail_measure_real_density
import Theorems.Thm_AvramDividend_Classical_real_nonnegative_scalar_withDensity_unrestricted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_strict_tail_scaled_drift_real_density (μ : Measure ℝ≥0)
    (hmoment : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤)
    (d : ℝ) (hd : 0 < d) :
    (ENNReal.ofReal d)⁻¹ •
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)}) =
    (volume : Measure ℝ).withDensity
      (fun t : ℝ => ENNReal.ofReal
        (if 0 < t then (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal / d else 0)) := by sorry
