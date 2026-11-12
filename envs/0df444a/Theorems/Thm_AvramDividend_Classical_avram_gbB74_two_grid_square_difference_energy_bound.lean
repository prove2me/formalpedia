-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB74_two_grid_square_difference_energy_bound
-- name    : AvramDividend.Classical.avram_gbB74_two_grid_square_difference_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:34:20.649166+00:00
-- url     : https://prove2.me/theorems/ee0186fb-d1eb-4db8-bc6f-a9457ebcda63
-- title:
--   Finite two-grid coefficient-square energy bounded by the separate energies
-- statement:
--   A deterministic Hilbert-space estimate needed to dominate original postpayment Gaussian grid coefficient differences: for any two real arrays on a finite common refinement, the sum of squared differences is at most twice the sum of their separate squared energies. This estimate applies to every original-space sample path without assuming the two grids are nested.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB74_two_grid_square_difference_energy_bound
    (N : ℕ) (a b : ℕ → ℝ) :
    (Finset.range N).sum (fun i => (a i - b i) ^ 2) ≤
      (Finset.range N).sum (fun i =>
        2 * (a i) ^ 2 + 2 * (b i) ^ 2) := by sorry
