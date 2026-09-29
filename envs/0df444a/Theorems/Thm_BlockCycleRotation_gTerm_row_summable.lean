-- Prove2me | Theorems.Thm_BlockCycleRotation_gTerm_row_summable
-- name    : BlockCycleRotation.gTerm_row_summable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:46.181386+00:00
-- url     : https://prove2.me/theorems/956beef9-d213-4d5c-be91-019f83c7cecd
-- title:
--   gTerm row summable
-- statement:
--   A supporting lemma of the formalization, declared as `gTerm_row_summable`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L186-L187

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.gTerm_row_summable (a : ℕ) : Summable (fun a' => gTerm (a, a')) := by sorry
