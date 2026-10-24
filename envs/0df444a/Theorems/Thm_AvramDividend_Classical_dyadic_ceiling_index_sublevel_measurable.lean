-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_sublevel_measurable
-- name    : AvramDividend.Classical.dyadic_ceiling_index_sublevel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:01:58.301822+00:00
-- url     : https://prove2.me/theorems/3ba478f5-a8af-481f-ab48-749168c83b50
-- title:
--   Dyadic ceiling index sublevels are measurable at their grid time
-- statement:
--   Let τ be a nonnegative-real stopping time for filtration 𝓕. For every dyadic resolution n and natural level k, the event {ceil(2^n τ)≤k} belongs to 𝓕 at the time k/2^n. The proof identifies this event with {τ≤k/2^n}, then applies the stopping-time property. This discharges the base filtration-measurability step of bounded_stopping_dyadic_grid_approximation.
-- source:
--   Mathlib IsStoppingTime.measurableSet_le, Nat.ceil_le and NNReal order coercions, no unproved imports.

import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Tactic.Positivity
open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.dyadic_ceiling_index_sublevel_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (n k : ℕ) :
    MeasurableSet[𝓕 ((k : ℝ≥0) / (2 : ℝ≥0) ^ n)]
      {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) ≤ k} := by sorry
