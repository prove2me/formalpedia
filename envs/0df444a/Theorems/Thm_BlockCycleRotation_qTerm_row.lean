-- Prove2me | Theorems.Thm_BlockCycleRotation_qTerm_row
-- name    : BlockCycleRotation.qTerm_row
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:23.037319+00:00
-- url     : https://prove2.me/theorems/39cd0537-2ddc-42ad-a366-d66e90a21aba
-- title:
--   The row sums give `H_n/n²`
-- statement:
--   **The row sums give `H_n/n²`.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L570-L585

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.qTerm_row (i : ℕ) : ∑' j : ℕ, qTerm (i, j) = harm (i + 2) / ((i : ℝ) + 1) ^ 2 := by sorry
