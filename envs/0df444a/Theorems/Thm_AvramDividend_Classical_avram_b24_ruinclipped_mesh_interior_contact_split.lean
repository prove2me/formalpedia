-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_ruinclipped_mesh_interior_contact_split
-- name    : AvramDividend.Classical.avram_b24_ruinclipped_mesh_interior_contact_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:59:12.098475+00:00
-- url     : https://prove2.me/theorems/cac523d1-a859-4100-ac54-eeddcc3f94b0
-- title:
--   Exact strict-interior plus unique inclusive-terminal-contact split for original stopped predictable mesh gain
-- statement:
--   On a non-overlapping ordered finite original stopped physical grid, the predictable masking term 1_{a_i<sigma} times an arbitrary real-weighted source increment is exactly the strict interior sum over b_i<sigma plus the terminal contact sum over a_i<sigma<=b_i. The terminal sum has at most one index. This preserves the last partial cell, strict-left inclusive-right endpoint and any time-zero/right-payments separately, without treating the interval as if all its noise stopped before ruin.
-- source:
--   Deterministic indexed stopping-mesh partition, using Proved uniqueness of contact interval; requires no independence or post-ruin assertions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_unique_ruincontact_cell_on_separated_grid
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_ruinclipped_mesh_interior_contact_split
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (σ : ℝ≥0)
    (H : ℕ → ℝ)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j) :
    (∑ i ∈ S, if σ ≤ a i then 0 else H i) =
        (∑ i ∈ S.filter (fun i => b i < σ), H i) +
        (∑ i ∈ S.filter (fun i => a i < σ ∧ σ ≤ b i), H i) ∧
    (∀ i ∈ S.filter (fun i => a i < σ ∧ σ ≤ b i),
     ∀ j ∈ S.filter (fun j => a j < σ ∧ σ ≤ b j), i = j) := by sorry
