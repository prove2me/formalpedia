-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_strict_tail_measure_real_density
-- name    : AvramDividend.Classical.positive_strict_tail_measure_real_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:42:26.733726+00:00
-- url     : https://prove2.me/theorems/24870e2e-dfa1-4622-bed6-ec0bd7e0a56e
-- title:
--   Strict positive jump-tail measure has its canonical real Lebesgue density
-- statement:
--   A nonnegative jump-magnitude measure with finite first moment has finite strict-tail mass at every positive threshold. The positive-half-line density measure built from its extended-real strict tail is therefore exactly the Lebesgue withDensity measure of the canonical real tail function, extended by zero on nonpositive arguments. This removes the existential Radon–Nikodym density mismatch in the bounded-variation Esscher zero-barrier renewal proof.
-- source:
--   Avram, Palmowski and Pistorius (2007), bounded-variation scale-function renewal kernel; accepted finite-positive-tail lemma e3dbca5f-3531-405a-9b14-be1cfb093d3c and pinned Mathlib withDensity_indicator.

import Theorems.Thm_AvramDividend_Classical_positive_tail_finite_of_finite_first_moment
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_strict_tail_measure_real_density
    (μ : Measure ℝ≥0)
    (hmoment : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)}) =
    volume.withDensity
      (fun t : ℝ =>
        ENNReal.ofReal (if 0 < t then
          (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal else 0)) := by sorry
