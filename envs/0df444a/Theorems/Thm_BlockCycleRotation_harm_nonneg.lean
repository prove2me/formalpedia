-- Prove2me | Theorems.Thm_BlockCycleRotation_harm_nonneg
-- name    : BlockCycleRotation.harm_nonneg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:58.102391+00:00
-- url     : https://prove2.me/theorems/f61ecf5d-f334-4aa1-8cda-f479843f7fd9
-- title:
--   harm nonneg
-- statement:
--   A supporting lemma of the formalization, declared as `harm_nonneg`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L344-L345

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.harm_nonneg (a : ℕ) : 0 ≤ harm a := by sorry
