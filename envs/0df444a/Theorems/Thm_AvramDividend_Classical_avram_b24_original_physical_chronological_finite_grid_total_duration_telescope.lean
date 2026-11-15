-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_physical_chronological_finite_grid_total_duration_telescope
-- name    : AvramDividend.Classical.avram_b24_original_physical_chronological_finite_grid_total_duration_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:42:50.452406+00:00
-- url     : https://prove2.me/theorems/1fabf2ad-17a5-4b0d-95e8-ffe2943af3ee
-- title:
--   Original finite chronological physical grid elapsed-time cell lengths telescope and sum to at most the full horizon
-- statement:
--   For the physical chronological grid times t_0,...,t_n of an actual stopped Itô-Meyer mesh, with the final time t_n≤T, the finite real sum of consecutive cell time increments exactly telescopes to t_n-t_0 and is therefore bounded by the physical horizon T. The identity is valid regardless of monotonicity; source grid constructions separately establish t_i≤t_{i+1} and disjoint half-open cells. This deterministic budget discharges the total elapsed time assumption in the original finite-activity compensated smallnegative mark source uniform all-grid L1 envelope theorem, including a right-inclusive stopping/ruin-contact final cell.
-- source:
--   Finite range telescoping of actual NNReal physical grid endpoints.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_physical_chronological_finite_grid_total_duration_telescope
    (t : ℕ → ℝ≥0) (n : ℕ) (T : ℝ≥0)
    (hn : t n ≤ T) :
    (∑ i ∈ Finset.range n,
      ((t (i + 1) : ℝ) - (t i : ℝ))) =
      (t n : ℝ) - (t 0 : ℝ) ∧
    (∑ i ∈ Finset.range n,
      ((t (i + 1) : ℝ) - (t i : ℝ))) ≤ (T : ℝ) := by sorry
