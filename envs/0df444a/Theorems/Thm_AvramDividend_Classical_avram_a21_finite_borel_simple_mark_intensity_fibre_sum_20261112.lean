-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_finite_borel_simple_mark_intensity_fibre_sum_20261112
-- name    : AvramDividend.Classical.avram_a21_finite_borel_simple_mark_intensity_fibre_sum_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:02:07.049388+00:00
-- url     : https://prove2.me/theorems/ce09bf6a-ada4-43c1-b7fd-dd3f411050bc
-- title:
--   Scaled finite Borel simple mark intensity equals physical fibre Poisson rates
-- statement:
--   For any measure finite on a measurable negative mark set and any uniformly bounded finite-range measurable real mark, the elapsed-time multiplied real integral of the mark equals the finite sum over each fibre of its value multiplied by the exact elapsed-time times fibre measure, converted from ENNReal to real.
-- source:
--   Proved spatial Borel real simple mark integral fibre partition 4c87924a-5472-47b3-ac1a-71926ecdd384 and ENNReal.toReal_mul; needed for original-space centred mark integral fibre decomposition.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_spatial_Borel_simple_mark_integral_partition
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_finite_borel_simple_mark_intensity_fibre_sum_20261112
    (ν : Measure ℝ) (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hMass : ν S < ⊤)
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    (T : ℝ) * (∫ z in S, g z ∂ν) =
      ∑ y ∈ g.range, y *
        (((T : ℝ≥0∞) * ν (S ∩ g ⁻¹' {y})).toReal) := by sorry
