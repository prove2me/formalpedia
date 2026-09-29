-- Prove2me | Theorems.Thm_BlockCycleRotation_tsum_tail_inv_sq
-- name    : BlockCycleRotation.tsum_tail_inv_sq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:56.201098+00:00
-- url     : https://prove2.me/theorems/1e652ce2-d85b-4a16-ae5c-c668d51e0050
-- title:
--   The tail of `∑ 1/m²` past `n`
-- statement:
--   The tail of `∑ 1/m²` past `n`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L435-L453

import Mathlib

open Real Finset Filter Topology

theorem BlockCycleRotation.tsum_tail_inv_sq {n : ℕ} (hn : 0 < n) :
    ∑' j : ℕ, 1 / ((n : ℝ) + (j : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) := by sorry
