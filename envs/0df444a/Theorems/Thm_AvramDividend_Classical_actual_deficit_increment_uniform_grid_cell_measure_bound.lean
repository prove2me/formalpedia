-- Prove2me | Theorems.Thm_AvramDividend_Classical_actual_deficit_increment_uniform_grid_cell_measure_bound
-- name    : AvramDividend.Classical.actual_deficit_increment_uniform_grid_cell_measure_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:56:28.868333+00:00
-- url     : https://prove2.me/theorems/a7f61839-4d6a-4bfc-a447-4371d790129f
-- title:
--   Equal-length actual Lévy grid cells inherit the same small-positive deficit probability bound
-- statement:
--   For the actual spectrally negative Lévy process, if every grid cell has length δ and the compensated drift deficit at time δ lies in (0,b] with probability at most u, then every grid-cell positive deficit increment bounded by b has probability at most u. This follows directly from stationarity of actual increments, with no independence hypothesis.
-- source:
--   Lévy stationary increments; Avram, Palmowski and Pistorius (2007), Section 3.3.

import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Real
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.actual_deficit_increment_uniform_grid_cell_measure_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (N : ℕ) (ts : ℕ → ℝ≥0) (δ : ℝ≥0)
    (b : ℝ) (u : ℝ≥0∞)
    (hStep : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hSpacing : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ)
    (hOne : P {ω : Ω |
      0 < X.drift * (δ : ℝ) - X.X δ ω ∧
      X.drift * (δ : ℝ) - X.X δ ω ≤ b} ≤ u) :
    ∀ k : ℕ, k < N →
      P {ω : Ω |
        0 < (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
          (X.drift * (ts k : ℝ) - X.X (ts k) ω) ∧
        (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
          (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤ b} ≤ u := by sorry
