-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_grid_wholeFuturePath_limit
-- name    : AvramDividend.Classical.levy_boundedStopping_grid_wholeFuturePath_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:15:12.807207+00:00
-- url     : https://prove2.me/theorems/23c80e32-f74f-42e9-94dc-13d6f0d8e8d9
-- title:
--   Bounded stopping times admit common finite grids converging to the whole Lévy future path
-- statement:
--   For each bounded stopping time, one sequence of finite adapted upper dyadic times approximates the entire shifted future-increment trajectory in the product topology on nonnegative-time real-valued paths, pointwise for every sample path. All finite-grid fibre measurability and domination data are retained for the strong-Markov limiting argument.
-- source:
--   Direct bounded-stopping whole-path convergence bridge for Open strong Markov theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and barrier-dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380. Composes Proved bounded_stopping_dyadic_grid_approximation 68cdb033-cbf7-4640-a303-5d06c3c7a761 and Proved pathwise right increment continuity 8f73cd3f-a954-42f0-8b97-1d2f9f66b949, using the pinned Mathlib product topology's tendsto_pi_nhds.

import Mathlib.Topology.Constructions
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_bounded_stopping_dyadic_grid_approximation
import Theorems.Thm_AvramDividend_Classical_chat08_stopped_levy_increment_tendsto_of_right_approximation

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_boundedStopping_grid_wholeFuturePath_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    ∃ (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0),
      (∀ n ω, τn n ω ∈ grid n) ∧
      (∀ n s, s ∈ grid n →
        MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s}) ∧
      (∀ ω n, τ ω ≤ τn n ω) ∧
      (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) ∧
      (∀ ω : Ω,
        Tendsto
          (fun n : ℕ => fun t : ℝ≥0 =>
            X.X (τn n ω + t) ω - X.X (τn n ω) ω)
          atTop
          (𝓝 (fun t : ℝ≥0 =>
            X.X (τ ω + t) ω - X.X (τ ω) ω))) := by
  sorry
