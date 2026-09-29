-- Prove2me | Theorems.Thm_BlockCycleRotation_abs_natCast_div_sub_le_one
-- name    : BlockCycleRotation.abs_natCast_div_sub_le_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:25.032833+00:00
-- url     : https://prove2.me/theorems/5af19fa8-97de-424a-9c69-a16ca2077055
-- title:
--   The floor is within `1` of the real quotient
-- statement:
--   **The floor is within `1` of the real quotient.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1487-L1493

import Mathlib

open Real Finset

theorem BlockCycleRotation.abs_natCast_div_sub_le_one {x y : ℕ} (hy : 0 < y) :
    |((x / y : ℕ) : ℝ) - (x : ℝ) / (y : ℝ)| ≤ 1 := by sorry
