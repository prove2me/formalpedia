-- Prove2me | Theorems.Thm_BlockCycleRotation_tendsto_window
-- name    : BlockCycleRotation.tendsto_window
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:47.49982+00:00
-- url     : https://prove2.me/theorems/7ded6316-be50-43b1-97f0-69fdc8d5d7dc
-- title:
--   The moving window of `n` terms tends to zero
-- statement:
--   The moving window of `n` terms tends to zero.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `tsum_telescope`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L370-L389

import Mathlib

open Real Finset Filter Topology

theorem BlockCycleRotation.tendsto_window (n : ℕ) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)) atTop (𝓝 0) := by sorry
