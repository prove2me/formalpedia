-- Prove2me | Theorems.Thm_AvramDividend_Classical_measurable_finite_mass_bin
-- name    : AvramDividend.Classical.measurable_finite_mass_bin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:36:55.030986+00:00
-- url     : https://prove2.me/theorems/1cc74373-b604-4acb-8fc0-31c28d8d00ed
-- title:
--   Mass bins for measurable extended-real random measure totals are measurable sample sets
-- statement:
--   For any measurable extended-nonnegative random mass and each natural index n, the subset of sample points where the mass is at most n+1 and either n is zero or the mass is strictly greater than n is measurable. These unit-length bins include zero in the first bin and permit a countable partition of every finite random mass. This is the sample-space measurability ingredient for constructing uniformly finite kernels from the original running-supremum dividend Stieltjes random measure.
-- source:
--   Pinned Mathlib measurableSet_Iic and measurableSet_Ioi, with the previously accepted runningSup_restrictedMass_measurable target 331155d2-26dd-4a42-ae9b-5b5e46827a1c as a forthcoming specialisation.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.measurable_finite_mass_bin
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (m : Ω → ℝ≥0∞) (hm : Measurable m) (n : ℕ) :
    MeasurableSet
      {ω : Ω | m ω ≤ (n + 1 : ℝ≥0∞) ∧
        (n = 0 ∨ (n : ℝ≥0∞) < m ω)} := by sorry
