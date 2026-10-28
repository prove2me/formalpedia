-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_atom_plus_real_density_full_cumulative
-- name    : AvramDividend.Classical.geometric_atom_plus_real_density_full_cumulative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:09:12.353976+00:00
-- url     : https://prove2.me/theorems/9249f2c7-28fc-42ed-b45a-5c8772b16d2c
-- title:
--   Full finite geometric renewal cumulative equals the atom coefficient plus the scaled real primitive
-- statement:
--   For a finite positive geometric renewal measure with no mass below zero, represented as a nonnegative scalar times a Dirac atom and a nonnegative real density, prove that its cumulative on (−∞,x] for x>0 equals its initial scalar atom r plus r times the integral of the real density on (0,x]. This packages the final measure-boundary arithmetic needed for zero-barrier Esscher scale identification.
-- source:
--   Proved geometric_atom_plus_real_density_zero_mass and geometric_atom_plus_real_density_positive_cumulative plus pinned Mathlib measure_union and ENNReal.toReal_add.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_geometric_atom_plus_real_density_zero_mass
import Theorems.Thm_AvramDividend_Classical_geometric_atom_plus_real_density_positive_cumulative

open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.geometric_atom_plus_real_density_full_cumulative
    (r : ℝ) (hr : 0 ≤ r) (f : ℝ → ℝ)
    (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (β : Measure ℝ)
    (hβ : β = ENNReal.ofReal r • (Measure.dirac (0 : ℝ) +
      volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))))
    (hβneg : β (Iio (0 : ℝ)) = 0)
    (hβfin : β Set.univ ≠ ⊤)
    (x : ℝ) (hx : 0 < x)
    (hfi : IntervalIntegrable f volume 0 x) :
    (β (Iic x)).toReal = r + r * ∫ y in (0 : ℝ)..x, f y  := by sorry
