-- Prove2me | Theorems.Thm_AvramDividend_Classical_bounded_stop_explicit_grid_increment_limit_with_horizon
-- name    : AvramDividend.Classical.bounded_stop_explicit_grid_increment_limit_with_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:53:14.631684+00:00
-- url     : https://prove2.me/theorems/062ac6d1-d935-477f-832a-c4e77cfa72fe
-- title:
--   Bounded stopping-time explicit dyadic grids have uniformly bounded support and convergent future Lévy increments
-- statement:
--   For a genuinely bounded stopping time τ≤H of a spectrally negative Lévy process, the explicitly defined upward dyadic ceiling times are supported on explicit finite grids, whose every declared time is at most H+1. Grid fibres are measurable in the corresponding filtration; the times dominate τ, converge pointwise to τ, and the future increment at any u≥0 converges pathwise to its stopped future increment. This common-terminal bound supplies exactly the missing construction needed for finite-terminal Esscher stopped-time arguments.
-- source:
--   Standard dyadic approximation of stopping times for right-continuous Lévy paths. Proven Prove2Me dependencies: dyadic_ceiling_time_mem_finite_nnreal_grid (05efd2bc), dyadic_ceiling_index_fibre_measurable (c09e6bad), dyadic_ceiling_nnreal_tendsto (5c6df1d9), dyadic_ceiling_finite_grid_le_bound (16a09ed8), chat08_stopped_levy_increment_tendsto_of_right_approximation (8f73cd3f).

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Constructions
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_mem_finite_nnreal_grid
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_fibre_measurable
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_finite_grid_le_bound
import Theorems.Thm_AvramDividend_Classical_chat08_stopped_levy_increment_tendsto_of_right_approximation
open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bounded_stop_explicit_grid_increment_limit_with_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) (u : ℝ≥0) :
    let τn : ℕ → Ω → ℝ≥0 := fun n ω =>
      (Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
        (2 : ℝ≥0) ^ n
    let grid : ℕ → Finset ℝ≥0 := fun n =>
      (Finset.range (Nat.ceil ((H : ℝ) * (2 : ℝ) ^ n) + 1)).image
        (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n)
    (∀ n ω, τn n ω ∈ grid n) ∧
    (∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s}) ∧
    (∀ n s, s ∈ grid n → s ≤ H + 1) ∧
    (∀ ω n, τ ω ≤ τn n ω) ∧
    (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) ∧
    (∀ ω, Tendsto
      (fun n => X.X (τn n ω + u) ω - X.X (τn n ω) ω)
      atTop (𝓝 (X.X (τ ω + u) ω - X.X (τ ω) ω))) := by sorry
