-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_contact_correction_crossing_support
-- name    : AvramDividend.Classical.avram_bv_strict12_original_contact_correction_crossing_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:39:16.2164+00:00
-- url     : https://prove2.me/theorems/e4b4dc93-9d3e-47ce-85fa-c661365cb630
-- title:
--   Original stopped residual contact correction is supported on ruin-crossing cells
-- statement:
--   An original masked physical-grid residual clipped at the ruin time differs from the raw finite-grid residual only in cells whose right endpoint lies beyond ruin. Gives the exact correction term, preserving source R and W.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict12_original_contact_correction_crossing_support
    (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0) (R : ℝ≥0 → ℝ)
    (W : ℕ → ℝ) (E : ℕ → Prop) :
    (∑ i ∈ Finset.range n,
      if E i then
        W i * (R (min (u (i + 1)) τ) - R (u (i + 1))) else 0) =
    (∑ i ∈ Finset.range n,
      if E i ∧ τ < u (i + 1) then
        W i * (R τ - R (u (i + 1))) else 0) := by sorry
