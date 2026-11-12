-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger147_clipped_final_discount_cell_absolute_bound
-- name    : AvramDividend.Classical.avram_gledger147_clipped_final_discount_cell_absolute_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:59:52.33121+00:00
-- url     : https://prove2.me/theorems/8d2170c6-4b90-4f79-a5ed-89b43a9762ce
-- title:
--   Final clipped discount crossing cell has absolute error at most discount times mesh width
-- statement:
--   For a nonnegative discount q, a nonnegative cell origin t and any stopped-cell remainder r between zero and the deterministic mesh width delta, the absolute discount factor change is at most q times delta. This is the boundary crossing term required for the original stopped Gaussian gledger139 absolute L1 discount Euler estimate.
-- source:
--   Exponential additivity, 1 minus exp(-q r) bounded by q r using pinned Real.add_one_le_exp, and monotonicity of the positive discount factor on nonnegative time.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gledger147_clipped_final_discount_cell_absolute_bound
    (q t r δ : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hrδ : r ≤ δ) :
    |Real.exp (-(q * (t + r))) - Real.exp (-(q * t))| ≤ q * δ := by sorry
