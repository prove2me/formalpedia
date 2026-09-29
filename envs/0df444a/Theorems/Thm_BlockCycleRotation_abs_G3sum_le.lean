-- Prove2me | Theorems.Thm_BlockCycleRotation_abs_G3sum_le
-- name    : BlockCycleRotation.abs_G3sum_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:19.473285+00:00
-- url     : https://prove2.me/theorems/4eb61ea0-f231-4b89-9dcd-57e69fdf8bb0
-- title:
--   abs G3sum le
-- statement:
--   A supporting lemma of the formalization, declared as `abs_G3sum_le`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `lemma_g_three`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem13.lean#L563-L614

import Definitions.Def_BlockCycleRotation_Theorem13
import Mathlib

open BlockCycleRotation
open Finset Real

theorem BlockCycleRotation.abs_G3sum_le {n : ℕ} (hn : 0 < n) : |G3sum n| ≤ Err n := by sorry
