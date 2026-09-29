-- Prove2me | Theorems.Thm_BlockCycleRotation_telescope_partial
-- name    : BlockCycleRotation.telescope_partial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:43.78905+00:00
-- url     : https://prove2.me/theorems/4e9f8e2e-9719-404f-8018-0920c7152c78
-- title:
--   The partial sums of the telescoping series
-- statement:
--   The partial sums of the telescoping series.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `tsum_telescope`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L347-L368

import Mathlib

open Real Finset Filter Topology

theorem BlockCycleRotation.telescope_partial (n N : ℕ) (h : n ≤ N) :
    ∑ j ∈ Finset.range N, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1))
      = (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1))
        - ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1) := by sorry
