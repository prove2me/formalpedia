-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_positive_horizon_fine_source_grid_witness
-- name    : AvramDividend.Classical.avram_wave6_01_positive_horizon_fine_source_grid_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:07:56.793052+00:00
-- url     : https://prove2.me/theorems/429cc0b0-bc23-4d62-8e59-6cad14faf68d
-- title:
--   Canonical positive-horizon nested fine grid witness for genuine source Lévy jump estimates
-- statement:
--   For any strictly positive NNReal horizon, construct the concrete deterministic uniform clocks grid(n,i)=i*T/n on the original nonnegative time axis. They are strictly increasing for n>0, start at zero, reach T at n, have mesh tending to zero, and all points i≤n stay below T. This discharges the non-physical auxiliary fine-grid assumptions in the already Proved original-path BV expected marked-count theorems; no stochastic model is replaced.
-- source:
--   Adapt the accepted explicit original-horizon uniform-grid construction from theorem 237842ca, prove hBound via monotonicity, and export a single reusable exists witness.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_positive_horizon_fine_source_grid_witness (T : ℝ≥0) (hT : 0 < T) :
    ∃ grid : ℕ → ℕ → ℝ≥0,
      (∀ n : ℕ, 0 < n →
        StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T) ∧
      (∀ δ : ℝ, 0 < δ →
        ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
          dist (grid n i) (grid n (i + 1)) < δ) ∧
      (∀ n i : ℕ, i ≤ n → grid n i ≤ T) := by sorry
