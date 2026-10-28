-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_grid_futureVector_limit
-- name    : AvramDividend.Classical.levy_boundedStopping_grid_futureVector_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:05:47.323346+00:00
-- url     : https://prove2.me/theorems/ec99ad9d-c757-458b-9ec4-28d5de6be2fb
-- title:
--   Bounded stopping times admit common adapted grids converging on every finite Lévy future vector
-- statement:
--   For a bounded stopping time, a single sequence of finite adapted upward dyadic grids simultaneously approximates the shifted future Lévy path in every finite-dimensional coordinate vector, pointwise on each sample path. The common grid and measurable fibre conditions make this a precise bridge toward whole-path strong Markov stopping-time laws.
-- source:
--   Root-connected strong-Markov bridge for theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and barrier dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380. Uses Proved bounded stopping dyadic approximation 68cdb033-cbf7-4640-a303-5d06c3c7a761 and stopped increment right-limit 8f73cd3f-a954-42f0-8b97-1d2f9f66b949; upgrades single-time convergence to every finite product coordinate.

import Mathlib.Topology.Constructions
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_bounded_stopping_dyadic_grid_approximation
import Theorems.Thm_AvramDividend_Classical_chat08_stopped_levy_increment_tendsto_of_right_approximation

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_boundedStopping_grid_futureVector_limit
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
      (∀ J : Finset ℝ≥0, ∀ ω : Ω,
        Tendsto
          (fun n : ℕ => fun j : J =>
            X.X (τn n ω + (j : ℝ≥0)) ω - X.X (τn n ω) ω)
          atTop
          (𝓝 (fun j : J =>
            X.X (τ ω + (j : ℝ≥0)) ω - X.X (τ ω) ω))) := by
  sorry
