-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
-- name    : AvramDividend.Classical.avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:11:05.497929+00:00
-- url     : https://prove2.me/theorems/83f438b9-3ced-4f77-9c2f-f96c313607f6
-- title:
--   Finite-support physical marked-jump series equals its causal finite sum at every earlier horizon
-- statement:
--   If all nonzero actual jump marks on a finite horizon form a specified finite set, then the complete causal marked-jump infinite series at any earlier time is exactly the finite sum of those supported marks with jump time no later than the observation time.
-- source:
--   Pinned Mathlib tsum_eq_sum and Finset.sum_congr; source-independent finite-support identity.

import Mathlib
open Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
    (a : ℝ≥0 → ℝ) (T : ℝ≥0) (S : Finset ℝ≥0)
    (hS : ∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ a u ≠ 0) :
    ∀ t : ℝ≥0, t ≤ T →
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then a u else 0) =
        ∑ u ∈ S, if u ≤ t then a u else 0 := by sorry
