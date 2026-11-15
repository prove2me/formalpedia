-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_finite_original_negative_mark_cutoff_sum_eventual_exact_limit
-- name    : AvramDividend.Classical.avram_b24_finite_original_negative_mark_cutoff_sum_eventual_exact_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:50:56.614966+00:00
-- url     : https://prove2.me/theorems/43b902cd-139d-4464-8f6e-525a4cb1c52b
-- title:
--   Every finite original negative-mark cutoff sum eventually equals the full surviving small-jump sum
-- statement:
--   For any finite family of real negative-mark jumps z_i, the original truncation indicator -1<z_i≤-1/(n+1) eventually agrees simultaneously across the entire finite family with the full negative-smallmark indicator -1<z_i<0. Consequently the finite cutoff jump sum converges to the exact complete smallmark jump sum, including mark values arbitrarily close to zero and excluding marks at or below -1. This is the pathwise finite-activity step needed to pass the exact marked-source cutoff identity to the original Jsmall limit without replacing it with a synthetic Lévy process.
-- source:
--   Pinned real reciprocal cutoff convergence, finite eventual conjunction and real limit uniqueness.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_finite_original_negative_mark_cutoff_sum_eventual_exact_limit
    {α : Type*} (S : Finset α) (z : α → ℝ) :
    Tendsto (fun n : ℕ =>
      ∑ i ∈ S, if -1 < z i ∧
        z i ≤ -(1 / ((n : ℝ) + 1)) then z i else 0)
      atTop (𝓝 (∑ i ∈ S, if -1 < z i ∧ z i < 0 then z i else 0)) := by sorry
