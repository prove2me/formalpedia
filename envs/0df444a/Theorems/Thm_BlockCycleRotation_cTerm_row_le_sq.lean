-- Prove2me | Theorems.Thm_BlockCycleRotation_cTerm_row_le_sq
-- name    : BlockCycleRotation.cTerm_row_le_sq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:30.859953+00:00
-- url     : https://prove2.me/theorems/31dc365f-be62-401b-9909-dba9940ec267
-- title:
--   Each row is at most `1/a²`
-- statement:
--   Each row is at most `1/a²`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `cConst_le_partial_add_sharp`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Bound.lean#L34-L47

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.cTerm_row_le_sq (a : ℕ) :
    ∑ a' ∈ Finset.range a, cTerm (a, a') ≤ 1 / (a : ℝ) ^ 2 := by sorry
