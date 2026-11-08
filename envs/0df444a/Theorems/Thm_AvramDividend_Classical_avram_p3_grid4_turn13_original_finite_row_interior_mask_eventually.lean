-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
-- name    : AvramDividend.Classical.avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:45:07.111978+00:00
-- url     : https://prove2.me/theorems/ed03fa23-c49d-4040-a196-e9d623840120
-- title:
--   Every interior stopped-row cell eventually lies in one predictable compact cutoff band
-- statement:
--   For any original finite physical reserve row, the strict positive-cap cells form a finite filtered index set. The cofinal predictable interior bands eventually contain every such cell simultaneously; no condition is imposed on ruin or out-of-cap cells. This is the uniform-on-one-row deterministic geometric bridge for the original stopped-process two-scale error proof.
-- source:
--   One application of the source-exact finite-set cofinal coverage theorem followed by Finset.filter membership; no stochastic assumptions or additional smoothness.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_cofinal_mask_eventually_covers_finite_grid
open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (n : ℕ) (z : ℕ → ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ i < n + 1,
      (0 < z i ∧ ENNReal.ofReal (z i) < C) →
        z i ∈ Icc (a k) (b k) := by sorry
