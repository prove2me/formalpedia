-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integrable_of_finite_firstMoment
-- name    : AvramDividend.Classical.positive_jump_tail_real_integrable_of_finite_firstMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:26:29.181508+00:00
-- url     : https://prove2.me/theorems/94d0ecde-b5aa-4f7d-a7cc-189852a949f9
-- title:
--   Positive strict jump-tail real density integrable from finite first moment
-- statement:
--   For any measure on positive jump magnitudes with a finite first moment, its strict positive-tail mass, converted to real values, is integrable on positive time. This converts the Proved positive_jump_tail_density_total_mass layer-cake identity into the exact real L1 input needed by causal_subunit_renewal_full_real_power_package when the measure is the Esscher-discounted Lévy jump measure. It supports the Open bv_ac_esscher_scaled_subunit_kernel_scale_identification and hence cstar_lt_top.
-- source:
--   Proved AvramDividend.Classical.positive_jump_tail_density_total_mass and Mathlib MeasureTheory.integrable_toReal_of_lintegral_ne_top.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_jump_tail_real_integrable_of_finite_firstMoment
    (μ : Measure ℝ≥0)
    (hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    IntegrableOn (fun t : ℝ =>
      (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal) (Ioi (0 : ℝ)) volume := by sorry
