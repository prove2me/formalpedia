-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_true_jump_support_reuse_horizon_for_all_earlier_mark_sums
-- name    : AvramDividend.Classical.avram_b24_original_true_jump_support_reuse_horizon_for_all_earlier_mark_sums
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:13:01.686196+00:00
-- url     : https://prove2.me/theorems/aa8d74d5-9f77-4572-8461-fe07e9c2534c
-- title:
--   One fixed finite original horizon jump-time support represents every earlier physical small negative marked jump sum
-- statement:
--   If S_T is the finite set of actual original nonzero Lévy jump times up to physical horizon T, and S_t is the actual set up to any t≤T, then the full original negative-smallmark sum over S_t is exactly the original finite marked cumulative causal step sum on the SINGLE fixed horizon support S_T with indicator u≤t. This lets the proved true all-time original intrinsic compensated Jsmall path representation be expressed with a fixed finite support, so that its true left time limit and terminal ruin-causing mark can be proved from Proved finite marked step limit and terminal atom theorems. No post-ruin assumption or synthetic marks.
-- source:
--   Original actual jump-time support extensional equality and pinned finset filtered sum algebra.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_true_jump_support_reuse_horizon_for_all_earlier_mark_sums
    (S_T S_t : Finset ℝ≥0) (z : ℝ≥0 → ℝ)
    (T t : ℝ≥0) (ht : t ≤ T)
    (hST : ∀ u : ℝ≥0, u ∈ S_T ↔ 0 < u ∧ u ≤ T ∧ z u ≠ 0)
    (hSt : ∀ u : ℝ≥0, u ∈ S_t ↔ 0 < u ∧ u ≤ t ∧ z u ≠ 0) :
    (∑ u ∈ S_t, if -1 < z u ∧ z u < 0 then z u else 0) =
    ∑ u ∈ S_T,
      if u ≤ t then (if -1 < z u ∧ z u < 0 then z u else 0) else 0 := by sorry
