-- Prove2me | Theorems.Thm_BlockCycleRotation_norm_e_sub_one_le
-- name    : BlockCycleRotation.norm_e_sub_one_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:03.18506+00:00
-- url     : https://prove2.me/theorems/e4fb9fad-a5d5-4380-964e-c53e69173ca4
-- title:
--   The easy half of Observation 17: `‖e θ - 1‖ ≤ |θ|`
-- statement:
--   The easy half of Observation 17: `‖e θ - 1‖ ≤ |θ|`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/ExpSum.lean#L62-L72

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.norm_e_sub_one_le (θ : ℝ) : ‖e θ - 1‖ ≤ |θ| := by sorry
