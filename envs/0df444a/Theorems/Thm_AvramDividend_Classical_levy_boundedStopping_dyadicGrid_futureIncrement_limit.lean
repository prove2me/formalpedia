-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_dyadicGrid_futureIncrement_limit
-- name    : AvramDividend.Classical.levy_boundedStopping_dyadicGrid_futureIncrement_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:00:55.771076+00:00
-- url     : https://prove2.me/theorems/a5003bf0-8116-4e30-8802-9de9be6f9d62
-- title:
--   Bounded stopping-time finite dyadic grids approximate future Lévy increments
-- statement:
--   Every bounded stopping time of the original filtration admits finite adapted dyadic upper approximations whose future Lévy increments converge pathwise at each nonnegative time. This combines an established finite-grid stopping approximation with right-continuous convergence of stopped process increments, retaining the adapted fibre conditions required for strong-Markov factorisation.
-- source:
--   Root-connected preparation for Prove2Me strong Markov child 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and barrier dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380. Composes Proved bounded_stopping_dyadic_grid_approximation 68cdb033-cbf7-4640-a303-5d06c3c7a761 and Proved chat08_stopped_levy_increment_tendsto_of_right_approximation 8f73cd3f-a954-42f0-8b97-1d2f9f66b949.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_bounded_stopping_dyadic_grid_approximation
import Theorems.Thm_AvramDividend_Classical_chat08_stopped_levy_increment_tendsto_of_right_approximation

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_boundedStopping_dyadicGrid_futureIncrement_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) (u : ℝ≥0) :
    ∃ (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0),
      (∀ n ω, τn n ω ∈ grid n) ∧
      (∀ n s, s ∈ grid n →
        MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s}) ∧
      (∀ ω n, τ ω ≤ τn n ω) ∧
      (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) ∧
      (∀ ω, Tendsto
        (fun n => X.X (τn n ω + u) ω - X.X (τn n ω) ω)
        atTop (𝓝 (X.X (τ ω + u) ω - X.X (τ ω) ω))) := by
  sorry
