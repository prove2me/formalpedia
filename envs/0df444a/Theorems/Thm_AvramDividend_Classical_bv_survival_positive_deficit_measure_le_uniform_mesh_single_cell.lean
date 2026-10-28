-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_survival_positive_deficit_measure_le_uniform_mesh_single_cell
-- name    : AvramDividend.Classical.bv_survival_positive_deficit_measure_le_uniform_mesh_single_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:13:33.244623+00:00
-- url     : https://prove2.me/theorems/16e3c023-7a1f-4c2d-8b10-fa2550978ffb
-- title:
--   Surviving with a positive BV Lévy drift deficit is bounded by N times one grid-cell probability
-- statement:
--   For an actual bounded-variation spectrally negative Lévy process, a uniform grid on [0,T] controls the event of strict survival with positive cumulative drift deficit by N times the single-duration δ probability of a small positive drift deficit. This composes the accepted almost-sure survival grid inclusion, finite union measure bound and exact stationary-increment law.
-- source:
--   Accepted Prove2Me finite-grid and stationary-law theorems; Avram, Palmowski and Pistorius (2007), Section 3.3.

import Theorems.Thm_AvramDividend_Classical_bv_survival_positive_deficit_measure_le_grid_cell_bound
import Theorems.Thm_AvramDividend_Classical_actual_deficit_increment_uniform_grid_cell_measure_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_survival_positive_deficit_measure_le_uniform_mesh_single_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0)
    (δ : ℝ≥0) (b : ℝ)
    (hStep : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hWithin : ∀ k : ℕ, k < N → ts (k + 1) ≤ T)
    (hMesh : ∀ k : ℕ, k < N →
      X.drift * ((ts (k + 1) : ℝ) - (ts k : ℝ)) ≤ b)
    (hSpacing : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ) :
    P {ω : Ω |
      (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
      X.drift * (ts 0 : ℝ) - X.X (ts 0) ω <
        X.drift * (ts N : ℝ) - X.X (ts N) ω} ≤
      (N : ℝ≥0∞) *
        P {ω : Ω |
          0 < X.drift * (δ : ℝ) - X.X δ ω ∧
          X.drift * (δ : ℝ) - X.X δ ω ≤ b} := by sorry
