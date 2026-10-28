-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_measure_cumulative_atom_integral_of_restrict_density
-- name    : AvramDividend.Classical.finite_measure_cumulative_atom_integral_of_restrict_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:14:17.364377+00:00
-- url     : https://prove2.me/theorems/442f28bb-cde0-4375-a39e-619393c51a9d
-- title:
--   Finite renewal measure with positive-side density has atom-plus-primitive cumulative
-- statement:
--   A finite measure whose restriction to the strictly positive half-line is the Lebesgue density measure of a nonnegative interval-integrable function has cumulative mass equal to its nonpositive-side mass plus the integral of that density. Removes the interval-by-interval density equality requirement and directly matches the measure restriction statement arising from renewal measure and density identification in the BV Esscher scale proof.

import Theorems.Thm_AvramDividend_Classical_finite_measure_cumulative_atom_integral_of_density
import Mathlib.MeasureTheory.Measure.WithDensity

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped ENNReal

theorem AvramDividend.Classical.finite_measure_cumulative_atom_integral_of_restrict_density
    (β : Measure ℝ) (hβfin : β Set.univ ≠ ⊤)
    (f : ℝ → ℝ) (hfnn : ∀ y : ℝ, 0 ≤ f y)
    (hβdensity :
      β.restrict (Ioi (0 : ℝ)) =
        (volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))).restrict
          (Ioi (0 : ℝ)))
    (hfi : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) :
    ∀ x : ℝ, 0 < x →
      (β (Iic x)).toReal =
        (β (Iic (0 : ℝ))).toReal + ∫ y in (0 : ℝ)..x, f y := by sorry
