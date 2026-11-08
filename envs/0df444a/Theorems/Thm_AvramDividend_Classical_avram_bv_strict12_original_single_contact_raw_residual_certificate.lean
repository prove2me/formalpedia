-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_single_contact_raw_residual_certificate
-- name    : AvramDividend.Classical.avram_bv_strict12_original_single_contact_raw_residual_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:56:12.501628+00:00
-- url     : https://prove2.me/theorems/13ee3d2d-e013-4d86-9d2e-aa8322e3d26d
-- title:
--   Original masked BV residual has at most one exact ruin-contact correction
-- statement:
--   The literal original bounded-variation finite physical-grid residual equals the ruin-clipped residual plus a correction which is either zero or exactly the raw residual over one uniquely crossing contact cell. It recombines source-exact algebraic reductions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_masked_stop_grid_residual_contact_identity
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_contact_correction_crossing_support
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_unique_ruin_contact_cell
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict12_original_single_contact_raw_residual_certificate
    (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0) (R : ℝ≥0 → ℝ)
    (W : ℕ → ℝ) (E : ℕ → Prop) (hmono : Monotone u)
    (hE : ∀ i, E i → u i < τ) :
    let Raw := ∑ i ∈ Finset.range n,
      if E i then W i * (R (u i) - R (u (i + 1))) else 0
    let Stopped := ∑ i ∈ Finset.range n,
      if E i then
        W i * (R (min (u i) τ) - R (min (u (i + 1)) τ)) else 0
    ∃ t : ℝ, Raw = Stopped + t ∧
      (t = 0 ∨ ∃ i ∈ Finset.range n,
        E i ∧ τ < u (i + 1) ∧
          t = W i * (R τ - R (u (i + 1)))) := by sorry
