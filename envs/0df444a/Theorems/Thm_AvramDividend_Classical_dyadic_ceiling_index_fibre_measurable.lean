-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_fibre_measurable
-- name    : AvramDividend.Classical.dyadic_ceiling_index_fibre_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:16:33.0467+00:00
-- url     : https://prove2.me/theorems/c09e6bad-9142-4c9c-9d4d-764cd63f2236
-- title:
--   Exact dyadic ceiling stopping-time fibres are measurable at their grid time
-- statement:
--   For every nonnegative-real stopping time τ, dyadic resolution n, and natural index k, the exact event {ceil(2^n τ)=k} is measurable at grid time k/2^n. The result follows by subtracting successive measurable sublevel events and using filtration monotonicity; the zero-index cell is handled separately.
-- source:
--   Depends on dyadic_ceiling_index_sublevel_measurable and Mathlib Filtration.mono; downstream bounded_stopping_dyadic_grid_approximation.

import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Tactic.Positivity
open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.dyadic_ceiling_index_fibre_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (n k : ℕ) :
    MeasurableSet[𝓕 ((k : ℝ≥0) / (2 : ℝ≥0) ^ n)]
      {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) = k} := by sorry
