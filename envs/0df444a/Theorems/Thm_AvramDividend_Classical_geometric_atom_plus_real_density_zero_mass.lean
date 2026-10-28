-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_atom_plus_real_density_zero_mass
-- name    : AvramDividend.Classical.geometric_atom_plus_real_density_zero_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:28:17.471992+00:00
-- url     : https://prove2.me/theorems/bebc7311-e28c-4a21-ab43-ad6cbb427953
-- title:
--   Initial atom of a scaled geometric renewal measure has its exact coefficient
-- statement:
--   For an arbitrary nonnegative real-density function, the density component charges no singleton. Consequently the value at the origin of a geometric renewal measure represented by a scaled Dirac atom plus an absolutely continuous component is exactly its scalar coefficient. This is the missing initial boundary term when converting a cumulative scale representation on [0,x] into a renewal primitive on (0,x].
-- source:
--   Mathlib withDensity_absolutelyContinuous and the Dirac singleton identity, adapted from the proved geometric_atom_plus_real_density_positive_cumulative.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.geometric_atom_plus_real_density_zero_mass (r : ℝ) (_hr : 0 ≤ r) (f : ℝ → ℝ)
    (β : Measure ℝ)
    (hβ : β = ENNReal.ofReal r • (Measure.dirac (0 : ℝ) +
      (volume : Measure ℝ).withDensity (fun x : ℝ => ENNReal.ofReal (f x)))) :
    β ({(0 : ℝ)} : Set ℝ) = ENNReal.ofReal r := by sorry
