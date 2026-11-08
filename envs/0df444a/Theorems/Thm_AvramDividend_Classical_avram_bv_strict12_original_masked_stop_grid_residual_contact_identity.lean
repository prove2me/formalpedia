-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_masked_stop_grid_residual_contact_identity
-- name    : AvramDividend.Classical.avram_bv_strict12_original_masked_stop_grid_residual_contact_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:36:22.052377+00:00
-- url     : https://prove2.me/theorems/41c5112b-5b61-4b57-82ee-249591f2fdca
-- title:
--   Exact original masked physical-grid residual and clipped ruin-contact decomposition
-- statement:
--   The original pre-ruin masked BV residual R(u_i)-R(u_i+1) splits cellwise into the stopped R increment and a residual contact correction supported at a ruin crossing; holds for all raw R and original physical-grid weights.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict12_original_masked_stop_grid_residual_contact_identity
    (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0) (R : ℝ≥0 → ℝ)
    (W : ℕ → ℝ) (E : ℕ → Prop)
    (hE : ∀ i, E i → u i < τ) :
    (∑ i ∈ Finset.range n,
      if E i then W i * (R (u i) - R (u (i + 1))) else 0) =
      (∑ i ∈ Finset.range n,
        if E i then
          W i * (R (min (u i) τ) - R (min (u (i + 1)) τ)) else 0) +
      (∑ i ∈ Finset.range n,
        if E i then
          W i * (R (min (u (i + 1)) τ) - R (u (i + 1))) else 0) := by sorry
