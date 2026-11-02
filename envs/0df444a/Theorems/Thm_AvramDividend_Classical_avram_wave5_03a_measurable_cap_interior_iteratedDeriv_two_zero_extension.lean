-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
-- name    : AvramDividend.Classical.avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:08:15.253524+00:00
-- url     : https://prove2.me/theorems/c521d276-f286-4df2-8a1f-4f9d9b758823
-- title:
--   Original capped interior smooth HJB Hessian has a measurable zero extension
-- statement:
--   For the exact finite-cap smoothness region {y : 0<y and ENNReal.ofReal y<C}, a C2 HJB test w has a measurable zero extension of the ordinary second iterated derivative. The interior set is open as an intersection of the positive halfline and a preimage under continuous ENNReal.ofReal. Mathlib ContDiffOn.continuousOn_iteratedDerivWithin and iteratedDerivWithin_of_isOpen provide continuousOn (iteratedDeriv 2 w) on that open set. Piecewise continuity then gives measurability. This is the exact second-derivative Hessian measurable integrand needed for the genuine original prepayment reserve's predictable Gaussian coefficient, with correct finite-cap region and no detached Brownian copy.

import Mathlib
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    Measurable (fun y : ℝ =>
      if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0) := by
  sorry
