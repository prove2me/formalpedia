-- Prove2me | Theorems.Thm_BlockCycleRotation_add_Outt_le_one
-- name    : BlockCycleRotation.add_Outt_le_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:50.944843+00:00
-- url     : https://prove2.me/theorems/ee3b4ef9-2204-4d25-b9e7-3136303b05a0
-- title:
--   `x + Out(x) ≤ 1` on `[0,1/2]`
-- statement:
--   **`x + Out(x) ≤ 1` on `[0,1/2]`.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `psiPartial_le_two`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L482-L499

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.add_Outt_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : x + Outt x ≤ 1 := by sorry
