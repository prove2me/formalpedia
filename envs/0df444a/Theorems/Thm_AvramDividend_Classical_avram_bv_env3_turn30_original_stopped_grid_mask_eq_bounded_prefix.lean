-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn30_original_stopped_grid_mask_eq_bounded_prefix
-- name    : AvramDividend.Classical.avram_bv_env3_turn30_original_stopped_grid_mask_eq_bounded_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:28:21.401986+00:00
-- url     : https://prove2.me/theorems/d046abd3-2849-4f6c-856c-58bdbf9c17db
-- title:
--   Original stopped physical-grid mask is exactly the bounded predictable prefix sum
-- statement:
--   An exact pathwise identity converts a finite physical-grid sum masked by strict pre-ruin times u_i<τ into the sum over an associated bounded integer prefix k(ω), provided the selector matches the strict clock tests pointwise. This accounts for boundary indices with equality at the ruin clock without dropping the last cell.
-- source:
--   Direct finite-set combinatorics: replace the selected-cell test by the prefix test and identify a filtered finite range with the shorter range using k≤m.

import Mathlib
open Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn30_original_stopped_grid_mask_eq_bounded_prefix
    {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (u : ℕ → ℝ≥0) (m : ℕ) (k : Ω → ℕ)
    (hkBound : ∀ ω, k ω ≤ m)
    (hMask : ∀ ω i, i < m →
      ((u i : WithTop ℝ≥0) < τ ω ↔ i < k ω))
    (Z : ℕ → Ω → ℝ) :
    ∀ ω, (∑ i ∈ Finset.range m,
        if (u i : WithTop ℝ≥0) < τ ω then Z i ω else 0)
      = ∑ i ∈ Finset.range (k ω), Z i ω := by sorry
