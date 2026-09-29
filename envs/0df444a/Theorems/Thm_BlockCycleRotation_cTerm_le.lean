-- Prove2me | Theorems.Thm_BlockCycleRotation_cTerm_le
-- name    : BlockCycleRotation.cTerm_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:12.785798+00:00
-- url     : https://prove2.me/theorems/51b0fc13-2539-47c5-befb-425fcced3c5e
-- title:
--   Termwise bound
-- statement:
--   **Termwise bound.** Each term is at most `3 / (2a³)`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `cTerm_row_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L38-L51

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.cTerm_le (p : ℕ × ℕ) : cTerm p ≤ 3 / (2 * (p.1 : ℝ) ^ 3) := by sorry
