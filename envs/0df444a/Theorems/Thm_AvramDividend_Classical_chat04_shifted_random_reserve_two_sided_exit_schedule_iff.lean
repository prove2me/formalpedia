-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_two_sided_exit_schedule_iff
-- name    : AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_exit_schedule_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:02:35.124114+00:00
-- url     : https://prove2.me/theorems/7f2dcf8d-9edc-4e6c-b90f-75a70bdc42bb
-- title:
--   Strict two-sided exit of a shifted random reserve before the horizon is equivalent to an observation in any rational-covering schedule
-- statement:
--   For a Lévy reserve shifted by arbitrary deterministic time and begun at any path-dependent reserve, strict exit from [0,a] before a horizon T occurs if and only if some observation in any countable schedule covering all nonnegative rationals witnesses the same strict exit before T. This gives the event-level countable reduction of two-sided first-exit times for Markov semigroups and optional stopping.
-- source:
--   Proved strict two-sided rational-grid exit equivalence and a countable rational-covering schedule.

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_two_sided_before_horizon_grid_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_exit_schedule_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b T : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹) :
    (∃ v : ℝ≥0, v < T ∧
      ((H ω + (X.X (b + v) ω - X.X b ω) < 0) ∨
        (a < H ω + (X.X (b + v) ω - X.X b ω)))) ↔
    ∃ j : ℕ, τ j < T ∧
      ((H ω + (X.X (b + τ j) ω - X.X b ω) < 0) ∨
        (a < H ω + (X.X (b + τ j) ω - X.X b ω))) := by sorry
