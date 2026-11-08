-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_discount_loss_total_at_most_one
-- name    : AvramDividend.Classical.avram_bv_residual9_discount_loss_total_at_most_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:26:45.865756+00:00
-- url     : https://prove2.me/theorems/5c3d70bc-1911-4518-aaa9-288823db6c99
-- title:
--   Original stopped physical-grid total discount-loss weights telescope to at most one
-- statement:
--   For the exact nonnegative original physical time grid starting at zero and nonnegative discount rate, discount losses telescope to one minus the final discount factor. Their sum belongs to [0,1]. This permits a single surviving ruin/contact negative post-value to control the whole discount commutator after separate localisation.
-- source:
--   AVRAM BV-RESIDUAL9 round-four discounted six-term original-cell analysis

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_discount_loss_total_at_most_one
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (m : ℕ) (h0 : u 0 = 0) :
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u i : ℝ))) -
        Real.exp (-(q * (u (i + 1) : ℝ))))) =
      1 - Real.exp (-(q * (u (m + 1) : ℝ))) ∧
    0 ≤ (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u i : ℝ))) -
        Real.exp (-(q * (u (i + 1) : ℝ))))) ∧
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u i : ℝ))) -
        Real.exp (-(q * (u (i + 1) : ℝ))))) ≤ 1 := by sorry
