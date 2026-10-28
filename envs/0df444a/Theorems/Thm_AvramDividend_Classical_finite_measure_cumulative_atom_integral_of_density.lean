-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_measure_cumulative_atom_integral_of_density
-- name    : AvramDividend.Classical.finite_measure_cumulative_atom_integral_of_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:09:05.379317+00:00
-- url     : https://prove2.me/theorems/461bd714-1b50-41ad-96c8-59365994a12c
-- title:
--   Finite renewal cumulative equals its zero-side mass plus integral of its positive-time density
-- statement:
--   For a finite real measure whose masses on every interval (0,x] agree with a nonnegative Lebesgue density, the real cumulative mass at x>0 is its nonpositive-side mass plus the ordinary integral of that density from zero to x. This is the precise measure-to-primitive bridge required to turn the established finite Esscher renewal measure identification into the integrated renewal density identity for the BV scale function.

import Theorems.Thm_AvramDividend_Classical_nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Real

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped ENNReal

theorem AvramDividend.Classical.finite_measure_cumulative_atom_integral_of_density
    (β : Measure ℝ) (hβfin : β Set.univ ≠ ⊤)
    (f : ℝ → ℝ) (hfnn : ∀ y : ℝ, 0 ≤ f y)
    (hIoc : ∀ x : ℝ, 0 ≤ x →
      β (Ioc (0 : ℝ) x) =
        (volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y)))
          (Ioc (0 : ℝ) x))
    (hfi : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) :
    ∀ x : ℝ, 0 < x →
      (β (Iic x)).toReal =
        (β (Iic (0 : ℝ))).toReal + ∫ y in (0 : ℝ)..x, f y := by sorry
