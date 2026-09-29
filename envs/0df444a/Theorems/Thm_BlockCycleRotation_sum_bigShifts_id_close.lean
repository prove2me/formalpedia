-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_bigShifts_id_close
-- name    : BlockCycleRotation.sum_bigShifts_id_close
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:14.43234+00:00
-- url     : https://prove2.me/theorems/3ca00c74-12a8-4786-89de-82c193ab8ac6
-- title:
--   `∑_{k > n/2} k` is `3n²/8` up to `n`
-- statement:
--   `∑_{k > n/2} k` is `3n²/8` up to `n`.
--
--   In Blomer–Bux this is **Remark 20**, “`∑_{k>n/2} k = 3n²/8 + O(n)`”. It is used in the proof of `remark_all_shifts`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 20. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/AllShifts.lean#L180-L194

import Definitions.Def_BlockCycleRotation_AllShifts
import Mathlib

open BlockCycleRotation
open Filter Topology Finset Real

theorem BlockCycleRotation.sum_bigShifts_id_close {n : ℕ} (hn : 0 < n) :
    |((∑ k ∈ bigShifts n, k : ℕ) : ℝ) - 3 * (n : ℝ) ^ 2 / 8| ≤ (n : ℝ) := by sorry
