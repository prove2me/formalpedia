-- Prove2me | Theorems.Thm_BlockCycleRotation_quadratic_diff
-- name    : BlockCycleRotation.quadratic_diff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:35.550898+00:00
-- url     : https://prove2.me/theorems/0b04fd27-2469-49f4-aab7-5ba61892a411
-- title:
--   The exact discrepancy of the quadratic main term
-- statement:
--   **The exact discrepancy of the quadratic main term.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1469-L1472

import Mathlib

open Real Finset

theorem BlockCycleRotation.quadratic_diff (A B U V : ℝ) :
    (A * (U - 1) + B * ((U - 1) * U / 2)) - (A * (V - 1) + B * ((V - 1) * V / 2))
      = (U - V) * (A + (B / 2) * (U + V - 1)) := by sorry
