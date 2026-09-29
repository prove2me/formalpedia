-- Prove2me | Theorems.Thm_BlockCycleRotation_fract_mul_le_half
-- name    : BlockCycleRotation.fract_mul_le_half
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:05:20.503677+00:00
-- url     : https://prove2.me/theorems/ed216f71-bd25-4dc0-a917-878bfa3c1caf
-- title:
--   `g·{1/g} ≤ 1/2`
-- statement:
--   **`g·{1/g} ≤ 1/2`** for `0 ≤ g < 1`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `seg_add_two_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Buffer.lean#L279-L295

import Mathlib

open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.fract_mul_le_half {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) :
    g * Int.fract (1 / g) ≤ 1 / 2 := by sorry
